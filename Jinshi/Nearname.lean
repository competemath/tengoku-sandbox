/-
nearname — a library name that is almost a name the tree already has (docs/jinshi.md, head N). A sneaky change hidden in a big PR
declares `Nat.add_com`, `Nat.Add_comm`, `Nat.add_comm1`, or `Nаt.succ'` with a Cyrillic а, and a reader skimming a statement that
uses it reads the seed's name. For every constant a library declares (okName, not the seed):

  1. homoglyphs (fail): a component holding a character outside ASCII that reads as an ASCII letter or digit (`confusable`, an
     explicit table), or an invisible one (`invisible`). Lowercase Greek, subscripts and primes are honest and not reported.
  2. near a seed name (warn): a suffix of the name with two or more components (the library's own leading namespace stripped one
     component at a time) that is a seed name once case, `'`, `_` and trailing digits are ignored, without being that name
     (identical is `shadow`'s business); or whose last component is one edit (insertion, deletion, substitution, adjacent
     transposition) from a seed name of the same namespace.
  3. the theorems of the library whose statements use a name found by 1 or 2.

The seed is indexed once per run, and only the namespaces the library's suffixes land in are indexed (by normalised full name,
and by the last component and each of its one-character deletions), so the cost is one pass over the seed and a few lookups per
library constant, whatever the size of the seed.
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

/-! ## nearname — a library name that is almost a seed name -/

/-- the non-ASCII characters that read as an ASCII letter or digit, by code point, with what each reads as -/
def confusableTable : List (UInt32 × Char) := [
  -- Cyrillic small: а е о р с х у і ј ѕ һ ԁ ԛ ԝ ѵ ӏ
  (0x0430, 'a'), (0x0435, 'e'), (0x043E, 'o'), (0x0440, 'p'), (0x0441, 'c'), (0x0445, 'x'), (0x0443, 'y'), (0x0456, 'i'),
  (0x0458, 'j'), (0x0455, 's'), (0x04BB, 'h'), (0x0501, 'd'), (0x051B, 'q'), (0x051D, 'w'), (0x0475, 'v'), (0x04CF, 'l'),
  -- Cyrillic capital: А В Е З К М Н О Р С Т Х У Ѕ І Ј Ԛ Ԝ Ѵ
  (0x0410, 'A'), (0x0412, 'B'), (0x0415, 'E'), (0x0417, '3'), (0x041A, 'K'), (0x041C, 'M'), (0x041D, 'H'), (0x041E, 'O'),
  (0x0420, 'P'), (0x0421, 'C'), (0x0422, 'T'), (0x0425, 'X'), (0x0423, 'Y'), (0x0405, 'S'), (0x0406, 'I'), (0x0408, 'J'),
  (0x051A, 'Q'), (0x051C, 'W'), (0x0474, 'V'),
  -- Greek capitals that look Latin: Α Β Ε Ζ Η Ι Κ Μ Ν Ο Ρ Τ Υ Χ (Lean admits them in identifiers); the small omicron ο
  (0x0391, 'A'), (0x0392, 'B'), (0x0395, 'E'), (0x0396, 'Z'), (0x0397, 'H'), (0x0399, 'I'), (0x039A, 'K'), (0x039C, 'M'),
  (0x039D, 'N'), (0x039F, 'O'), (0x03A1, 'P'), (0x03A4, 'T'), (0x03A5, 'Y'), (0x03A7, 'X'), (0x03BF, 'o'),
  -- Latin look-alikes: ı ȷ ɑ ɡ ⅼ; Armenian օ
  (0x0131, 'i'), (0x0237, 'j'), (0x0251, 'a'), (0x0261, 'g'), (0x217C, 'l'), (0x0585, 'o')]

/-- the ASCII letter or digit a character reads as, when it is not that character: the table, the fullwidth forms, and the
mathematical bold/italic/sans-serif/monospace Latin letters and digits (script, fraktur and double-struck look like what they
are and are not here) -/
def confusable (ch : Char) : Option Char :=
  let v := ch.val
  if v < 0x80 then none
  else if 0xFF21 ≤ v && v ≤ 0xFF3A then some (Char.ofNat (v - 0xFF21 + 0x41).toNat)   -- fullwidth A–Z
  else if 0xFF41 ≤ v && v ≤ 0xFF5A then some (Char.ofNat (v - 0xFF41 + 0x61).toNat)   -- fullwidth a–z
  else if 0xFF10 ≤ v && v ≤ 0xFF19 then some (Char.ofNat (v - 0xFF10 + 0x30).toNat)   -- fullwidth 0–9
  else if (0x1D400 ≤ v && v ≤ 0x1D49B) || (0x1D5A0 ≤ v && v ≤ 0x1D6A3) then           -- mathematical Latin, 52 per style
    let k := (v - 0x1D400) % 52
    some (Char.ofNat (if k < 26 then 0x41 + k else 0x61 + k - 26).toNat)
  else if 0x1D7CE ≤ v && v ≤ 0x1D7FF then some (Char.ofNat (0x30 + (v - 0x1D7CE) % 10).toNat)  -- mathematical digits
  else (confusableTable.find? (·.1 == v)).map (·.2)

/-- a character that shows nothing: zero-width spaces and joiners, word joiner, byte-order mark, soft hyphen, the bidi controls
(a bidi override reorders what a reader sees), the combining grapheme joiner, the Mongolian vowel separator -/
def invisible (ch : Char) : Bool :=
  let v := ch.val
  (0x200B ≤ v && v ≤ 0x200F) || (0x202A ≤ v && v ≤ 0x202E) || (0x2060 ≤ v && v ≤ 0x2064) || (0x2066 ≤ v && v ≤ 0x2069) ||
    v == 0xFEFF || v == 0x00AD || v == 0x034F || v == 0x180E || v == 0x061C

def codePoint (ch : Char) : String :=
  let h := String.ofList ((Nat.toDigits 16 ch.val.toNat).map Char.toUpper)
  "U+" ++ "".pushn '0' (4 - min 4 h.length) ++ h

/-- `some (what is wrong, the name as a reader sees it)` when a component of the name holds a confusable or invisible character -/
def homoglyphReport (n : Name) : Option (String × Name) :=
  let cs := n.components
  let bad := cs.flatMap fun c => match c with
    | .str _ s => s.toList.filterMap fun ch =>
        if invisible ch then some s!"an invisible {codePoint ch} in `{s}`"
        else (confusable ch).map fun a => s!"{ch} ({codePoint ch}) that reads as `{a}` in `{s}`"
    | _ => []
  if bad.isEmpty then none else
  let reads := cs.foldl (init := Name.anonymous) fun acc c => match c with
    | .str _ s => Name.str acc (String.ofList (s.toList.filterMap fun ch => if invisible ch then none else some ((confusable ch).getD ch)))
    | .num _ k => Name.num acc k
    | .anonymous => acc
  some (", ".intercalate bad, reads)

/-- every suffix of the name with two or more components, the name itself first -/
def suffixes₂ (n : Name) : List Name :=
  let cs := n.components
  (List.range (cs.length - 1)).map fun k => (cs.drop k).foldl (fun acc c => acc ++ c) Name.anonymous

/-- lowercase, `'` and `_` dropped, trailing digits dropped -/
def normComponent (s : String) : String :=
  let cs := (s.toList.filter fun ch => ch != '\'' && ch != '_').map Char.toLower
  String.ofList (cs.reverse.dropWhile Char.isDigit).reverse

/-- the name with every component normalised; none when a component is numeric or normalises to nothing -/
def normName (n : Name) : Option String := do
  let parts ← n.components.mapM fun c => match c with
    | .str _ s => let t := normComponent s; if t.isEmpty then none else some t
    | _ => none
  return ".".intercalate parts

def lastStr : Name → Option String
  | .str _ s => some s
  | _ => none

/-- the string with one character removed, at each position -/
def deletions (s : String) : List String :=
  let cs := s.toList
  (List.range cs.length).map fun i => String.ofList (cs.take i ++ cs.drop (i + 1))

/-- exactly one edit apart: an insertion, a deletion, a substitution, or an adjacent transposition (Damerau–Levenshtein distance 1) -/
def oneEditApart (a b : String) : Bool :=
  let (xs, ys) := dropCommon a.toList b.toList
  let (xs, ys) := dropCommon xs.reverse ys.reverse
  match xs, ys with
  | [_], [] | [], [_] | [_], [_] => true
  | [c, d], [d', c'] => c == c' && d == d'
  | _, _ => false
where
  dropCommon : List Char → List Char → List Char × List Char
    | x :: xs, y :: ys => if x == y then dropCommon xs ys else (x :: xs, y :: ys)
    | xs, ys => (xs, ys)

/-- the seed, indexed for the two tests; only the namespaces the library's suffixes land in are indexed -/
structure SeedIndex where
  /-- normalised full name → a seed name -/
  byNorm : Std.HashMap String Name := {}
  /-- `namespace/variant`, the variant the last component or one of its one-character deletions → the seed names -/
  byDeletion : Std.HashMap String (Array Name) := {}

def seedIndex (c : Ctx) (env : Environment) (nsNorm : Std.HashSet String) (nsExact : NameSet) : SeedIndex :=
  env.constants.fold (init := {}) fun ix n _ =>
    if !okName n || !isSeedOrCore c env n then ix else
    let p := n.getPrefix
    let ix := match normName p, normName n with
      | some np, some nn => if nsNorm.contains np then { ix with byNorm := ix.byNorm.insertIfNew nn n } else ix
      | _, _ => ix
    if !nsExact.contains p then ix else
    match lastStr n with
    | some s =>
      let ps := p.toString
      { ix with byDeletion := (s :: deletions s).foldl (init := ix.byDeletion) fun m v =>
          m.alter s!"{ps}/{v}" fun o => some ((o.getD #[]).push n) }
    | none => ix

def nearname (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let lib := (selected c env).filter fun (m, n, _) => !c.seed.isPrefixOf m && okName n
  -- the namespaces the library's names land in once their own leading components are stripped
  let mut nsNorm : Std.HashSet String := {}
  let mut nsExact : NameSet := {}
  for (_, n, _) in lib do
    for s in suffixes₂ n do
      let p := s.getPrefix
      nsExact := nsExact.insert p
      if let some np := normName p then nsNorm := nsNorm.insert np
  let ix := seedIndex c env nsNorm nsExact
  let mut near : NameMap String := {}  -- a library name found by 1 or 2 → what it is near, for the theorems
  let mut out := #[]
  for (m, n, _) in lib do
    -- 1. homoglyphs
    if let some (why, reads) := homoglyphReport n then
      let tree := match (reads :: suffixes₂ reads).find? env.contains with
        | some r => s!"; `{r}` is a name of the tree ({(moduleOf env r).getD `_})"
        | none => ""
      near := near.insert n s!"reads as {reads}"
      out := out.push { check := "nearname", severity := "fail", module := m, name := n, line := ← lineOf n,
                        detail := s!"the name holds {why}: it reads as `{reads}` and is not it{tree}" }
      continue
    -- 2. near a seed name
    let mut hit : Option (Name × String) := none
    for s in suffixes₂ n do
      if env.contains s then continue  -- identical to a name of the tree: shadow's business
      if let some key := normName s then
        if let some t := ix.byNorm[key]? then
          if t != s then
            hit := some (t, "the same name up to case, primes, underscores and trailing digits as")
            break
      if let some last := lastStr s then
        if last.length ≥ 3 then
          let ps := s.getPrefix.toString
          for v in last :: deletions last do
            if let some ts := ix.byDeletion[s!"{ps}/{v}"]? then
              for t in ts do
                if t != s then
                  if let some tl := lastStr t then
                    if oneEditApart last tl then
                      hit := some (t, "one edit away from")
                      break
            if hit.isSome then break
      if hit.isSome then break
    if let some (t, how) := hit then
      near := near.insert n s!"near {t}"
      out := out.push { check := "nearname", severity := "warn", module := m, name := n, line := ← lineOf n,
                        detail := s!"declares `{n}`, {how} the seed's `{t}` ({(moduleOf env t).getD `_}): a reader of a statement that uses it reads the seed's name" }
  -- 3. the theorems whose statements use a near name
  for (m, n, ci) in lib do
    let .thmInfo _ := ci | continue
    let used := ci.type.getUsedConstants.filter near.contains
    unless used.isEmpty do
      out := out.push { check := "nearname", severity := "warn", module := m, name := n, line := ← lineOf n,
                        detail := s!"statement uses {used.toList.map fun k => s!"{k} ({(near.find? k).getD ""})"}" }
  return out

end Jinshi
