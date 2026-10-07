-- jinshi: only roundtrip
/-
Jinshi fixture for `roundtrip` (docs/jinshi.md): a statement is shown to a reader by the pretty printer; read back and
re-elaborated, it must be the statement the kernel checked. Compiled against Lean's own library; Roundtrip.expected.tsv names
what must be found, everything else here must stay quiet.
-/
namespace JinshiFixtures

-- quiet: an ordinary statement round-trips
theorem fine (n : Nat) : n + 0 = n := Nat.add_zero n

-- quiet: a `local notation` is gone from the printer and from the parser alike once the section ends, so the statement is
-- shown as `1 + 1 = 2` and reads back as that; a global `notation` is kept by both. Neither can disagree with itself.
section
local notation "𝟙" => (1 : Nat)
theorem shown : 𝟙 + 𝟙 = 2 := rfl
end

-- does not parse: a private definition in a public statement is shown as `hidden✝`, which no reader can type or look up
private def hidden : Nat := 3
theorem usesPrivate : hidden = 3 := rfl

-- does not elaborate: a proof inside the statement is shown as `⋯` (pp.proofs is off by default): the reader cannot know
-- which proof, and the text cannot be elaborated
theorem withProof : (⟨2, by decide⟩ : { n : Nat // n > 1 }).val = 2 := rfl

-- a different statement: the `+` the reader sees is `Nat.add`, the `+` the kernel checked is the instance `weird`, whose
-- `a + b` is `a`; the text `a + b = a` is a false claim about numbers, proved about another operation
set_option warn.classDefReducibility false in
def weird : Add Nat := ⟨fun a _ => a⟩
theorem hiddenInstance (a b : Nat) : @HAdd.hAdd Nat Nat Nat (@instHAdd Nat weird) a b = a := rfl

-- a different statement: shown as `2 + 2 = 4`, which reads back over `Nat`; proved over `Int`
theorem intNumerals : (2 : Int) + 2 = 4 := rfl

end JinshiFixtures
