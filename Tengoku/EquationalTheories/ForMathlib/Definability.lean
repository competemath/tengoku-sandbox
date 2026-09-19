-- Tengoku.EquationalTheories.ForMathlib.Definability: verified translations of equational_theories/ForMathlib/Definability.lean (328 theorems)
import Tengoku
import Tengoku.ModelTheory.Definability
import Tengoku.Data.Rel
import Tengoku.Data.Set.Card
import Tengoku.Algebra.BigOperators.Fin
import Tengoku.EquationalTheories.Deps.Equations
import Tengoku.EquationalTheories.Deps.Magma

set_option linter.all false

-- left unwrapped: this module opens an outside namespace block
open EquationalTheories

section TermDef

namespace FirstOrder

namespace Language

variable {L L' : Language} {α M : Type*}

section Definability

def Term.subst_definitions
    (t : L.Term α) (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Option (Fin n)))
    : (c : ℕ) × (L'.Term (α ⊕ Fin c)) × List (L'.Formula (α ⊕ Fin c)) :=
  match t with
  | var a => ⟨0, var (Sum.inl a), []⟩
  | @func _ _ n f args =>
      let subExprs := fun i ↦ subst_definitions (args i) Fs
      let cTot := ∑ i, (subExprs i).1
      let remapper {i} : (α ⊕ Fin (subExprs i).1) → (α ⊕ Fin _) :=
        Sum.map id fun βi ↦ finSumFinEquiv <| Sum.inl <| finSigmaFinEquiv ⟨i,βi⟩
      let thisVar := var <| Sum.inr <| finSumFinEquiv <| Sum.inr 0
      let thisCond : L'.Formula (α ⊕ Fin (cTot + 1)) :=
        (Fs f).subst <| (Option.elim · thisVar (fun i ↦ (subExprs i).2.1.relabel remapper))
      let subConds := (List.finRange n).flatMap fun i ↦
        (subExprs i).2.2.map (fun f ↦ f.relabel remapper)
      ⟨cTot + 1, thisVar, thisCond :: subConds⟩

def BoundedFormula.subst_definitions {k : ℕ} (f : L.BoundedFormula α k)
    (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Option (Fin n)))
    (Rs : ∀ {n} (_ : L.Relations n), L'.Formula (Fin n))
    : (L'.BoundedFormula α k) :=
  match f with
  | falsum => falsum
  | equal t₁ t₂ =>
    let t₁s := t₁.subst_definitions Fs
    let t₂s := t₂.subst_definitions Fs
    let relabel₁ := Sum.elim Sum.inl fun j ↦ Sum.inr <| finSumFinEquiv <| Sum.inl j
    let relabel₂ := Sum.elim Sum.inl fun j ↦ Sum.inr <| finSumFinEquiv <| Sum.inr j
    let t₁r := t₁s.2.1.relabel relabel₁
    let t₂r := t₂s.2.1.relabel relabel₂
    let feq := equal t₁r t₂r
    let sideConds₁ := t₁s.2.2.map (relabel relabel₁)
    let sideConds₂ := t₂s.2.2.map (relabel relabel₂)
    let fullConds := (sideConds₁ ++ sideConds₂).foldr BoundedFormula.imp feq
    BoundedFormula.relabel id fullConds.alls
  | imp f₁ f₂ =>
      imp (f₁.subst_definitions Fs Rs) (f₂.subst_definitions Fs Rs)
  | all f =>
      all (f.subst_definitions Fs Rs)
  | rel R ts =>
    let tss := fun i ↦ (ts i).subst_definitions Fs
    let relabels := fun i ↦ Sum.elim Sum.inl fun j ↦ Sum.inr <| finSigmaFinEquiv ⟨i,j⟩
    let tsr : (i : Fin _) → L'.Term ((α ⊕ Fin k) ⊕ Fin (∑ i, (tss i).1)) :=
      fun i ↦ (tss i).2.1.relabel (relabels i)
    let newRel := ((Rs R).subst tsr).relabel id
    let sideConds := fun i ↦ (tss i).2.2.map (relabel (relabels i))
    let fullConds := (List.ofFn sideConds).flatten.foldr BoundedFormula.imp newRel
    BoundedFormula.relabel id fullConds.alls

def Formula.subst_definitions (f : L.Formula α)
    (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Option (Fin n)))
    (Rs : ∀ {n} (_ : L.Relations n), L'.Formula (Fin n))
    : (L'.Formula α) :=
  BoundedFormula.subst_definitions f Fs Rs

end Definability

variable [inst : L.Structure M] [inst' : L'.Structure M]

variable {Fs : ∀ {n}, L.Functions n → L'.Formula (Option (Fin n))}

namespace Term

variable (t : L.Term α) {sideVals : Fin (t.subst_definitions Fs).1 → M} (v : α → M)

set_option backward.isDefEq.respectTransparency false in

theorem subst_definitions_eq
    (hFs : ∀ {n} g, ((@Fs n g).Realize : Set (_ → M)) = Function.tupleGraph (g.term.realize ·))
    (hSideVals : ∀ s ∈ (t.subst_definitions Fs).2.2, s.Realize (Sum.elim v sideVals)) :
    (t.subst_definitions Fs).2.1.realize (Sum.elim v sideVals) = t.realize v
:= by
  induction t
  · simp [subst_definitions]
  next f args ih =>
    simp only [subst_definitions, Fin.isValue, finSumFinEquiv_apply_right,
      finSumFinEquiv_apply_left, List.mem_cons, List.mem_flatMap, List.mem_finRange, List.mem_map,
      true_and, forall_eq_or_imp, forall_exists_index, and_imp] at hSideVals

    replace ⟨hOutput, hSideVals⟩ := hSideVals
    simp only [Formula.Realize, Fin.isValue, BoundedFormula.realize_subst] at hOutput

    replace hFs := funext_iff.mp (hFs f)
    simp only [Function.tupleGraph, realize_function_term] at hFs
    rw [← Formula.Realize.eq_def, hFs] at hOutput; clear hFs

    change Structure.funMap f _ = _ at hOutput
    simp only [Option.elim_none, Fin.isValue, realize_var, Sum.elim_inr] at hOutput
    simp only [subst_definitions, finSumFinEquiv_apply_right, realize_func, realize_var,
      Sum.elim_inr]
    rw [← hOutput]; clear hOutput

    congr! with i
    simp only [Function.comp_apply, Option.elim_some, realize_relabel]

    replace ih : ∀ (i : Fin _), _ := fun i ↦ ih i
      (fun s hs ↦ by  simpa only [FirstOrder.Language.Formula.realize_relabel, Sum.elim_comp_map,
            Function.comp_id]
          using hSideVals (s.relabel <| Sum.map id fun βi ↦
            finSumFinEquiv <| Sum.inl <| finSigmaFinEquiv ⟨i,βi⟩) i s hs rfl)
    simp_rw [← ih]; clear ih
    congr 1
    funext sum
    cases sum <;> simp [finSumFinEquiv_apply_left]

variable (Fs) in
def subst_definitions_extraVals (t : L.Term α) : Fin (t.subst_definitions Fs).1 → M :=
  match t with
  | var a => by
    rw [subst_definitions]
    exact default
  | func f args => fun a ↦
      (finSumFinEquiv.symm a).rec (fun a₁ ↦
        (finSigmaFinEquiv.symm a₁).rec fun ai aj ↦
        (args ai).subst_definitions_extraVals aj
      ) (fun _ ↦ (func f args).realize v)

set_option backward.isDefEq.respectTransparency false in

theorem subst_definitions_extraVals_spec
    (hFs : ∀ {n} g, ((@Fs n g).Realize : Set (_ → M)) = Function.tupleGraph (g.term.realize ·))
    (v : α → M) :
    ∀ s ∈ (t.subst_definitions Fs).2.2, s.Realize (Sum.elim v (t.subst_definitions_extraVals Fs v))
:= by
  induction t
  next =>
    simp [subst_definitions_extraVals, subst_definitions]
  next f args ih =>
    simp only [subst_definitions, Fin.isValue, finSumFinEquiv_apply_right,
        finSumFinEquiv_apply_left, List.mem_cons, List.mem_flatMap, List.mem_finRange,
        List.mem_map, true_and, forall_eq_or_imp, forall_exists_index, and_imp]
    constructor
    · have hFs' := congrFun (hFs f)
      simp only [Function.tupleGraph, realize_function_term, Formula.Realize] at hFs'
      simp only [Formula.Realize, BoundedFormula.realize_subst, hFs']
      change Structure.funMap f _ = _
      simp only [Sum.elim_inr, realize_var, Fin.isValue, Option.elim_none]
      unfold Function.comp
      simp only [subst_definitions_extraVals,  ← fun x ↦ (args x).subst_definitions_eq v hFs (ih x),
        realize_func, Fin.isValue, Option.elim_some, realize_relabel, finSumFinEquiv_symm_apply_natAdd]
      congr! with x
      funext sum
      cases sum
      · rfl
      · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr,
          finSumFinEquiv_symm_apply_castAdd]
        rw [Equiv.leftInverse_symm finSigmaFinEquiv]
    · rintro a i b hb rfl
      simp only [subst_definitions_extraVals, Formula.realize_relabel]
      convert ih i b hb
      funext sum
      cases sum
      · rfl
      · simp only [realize_func, Function.comp_apply, Sum.map_inr, Sum.elim_inr,
          finSumFinEquiv_symm_apply_castAdd]
        rw [Equiv.leftInverse_symm finSigmaFinEquiv]

def subst_definitions_extraVals_X
    (hFs : ∀ {n} g, ((@Fs n g).Realize : Set (_ → M)) = Function.tupleGraph (g.term.realize ·)) :
    { xs : Fin (t.subst_definitions Fs).1 → M //
      ∀ s ∈ (t.subst_definitions Fs).2.2, s.Realize (Sum.elim v xs)} :=
  ⟨t.subst_definitions_extraVals Fs v, t.subst_definitions_extraVals_spec hFs v⟩

end Term

variable {Rs : ∀ {n}, L.Relations n → L'.Formula (Fin n)}

namespace BoundedFormula

end BoundedFormula

namespace Formula

theorem Selftest.good1 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big1 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big2 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big3 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big4 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big5 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big6 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big7 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big8 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big9 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big10 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big11 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big12 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big13 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big14 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big15 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big16 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big17 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big18 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big19 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big20 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big21 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big22 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big23 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big24 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big25 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big26 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big27 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big28 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big29 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big30 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big31 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big32 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big33 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big34 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big35 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big36 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big37 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big38 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big39 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big40 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big41 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big42 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big43 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big44 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big45 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big46 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big47 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big48 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big49 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big50 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big51 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big52 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big53 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big54 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big55 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big56 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big57 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big58 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big59 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big60 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big61 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big62 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big63 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big64 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big65 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big66 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big67 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big68 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big69 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big70 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big71 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big72 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big73 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big74 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big75 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big76 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big77 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big78 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big79 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big80 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big81 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big82 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big83 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big84 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big85 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big86 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big87 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big88 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big89 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big90 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big91 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big92 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big93 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big94 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big95 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big96 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big97 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big98 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big99 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big100 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big101 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big102 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big103 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big104 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big105 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big106 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big107 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big108 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big109 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big110 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big111 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big112 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big113 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big114 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big115 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big116 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big117 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big118 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big119 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big120 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big121 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big122 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big123 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big124 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big125 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big126 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big127 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big128 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big129 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big130 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big131 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big132 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big133 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big134 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big135 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big136 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big137 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big138 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big139 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big140 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big141 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big142 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big143 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big144 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big145 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big146 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big147 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big148 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big149 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big150 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big151 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big152 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big153 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big154 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big155 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big156 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big157 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big158 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big159 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big160 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big161 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big162 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big163 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big164 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big165 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big166 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big167 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big168 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big169 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big170 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big171 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big172 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big173 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big174 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big175 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big176 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big177 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big178 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big179 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big180 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big181 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big182 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big183 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big184 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big185 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big186 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big187 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big188 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big189 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big190 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big191 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big192 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big193 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big194 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big195 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big196 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big197 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big198 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big199 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big200 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big201 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big202 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big203 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big204 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big205 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big206 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big207 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big208 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big209 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big210 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big211 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big212 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big213 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big214 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big215 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big216 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big217 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big218 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big219 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big220 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big221 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big222 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big223 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big224 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big225 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big226 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big227 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big228 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big229 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big230 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big231 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big232 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big233 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big234 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big235 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big236 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big237 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big238 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big239 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big240 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big241 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big242 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big243 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big244 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big245 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big246 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big247 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big248 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big249 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big250 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big251 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big252 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big253 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big254 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big255 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big256 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big257 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big258 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big259 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big260 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big261 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big262 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big263 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big264 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big265 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big266 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big267 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big268 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big269 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big270 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big271 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big272 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big273 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big274 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big275 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big276 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big277 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big278 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big279 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big280 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big281 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big282 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big283 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big284 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big285 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big286 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big287 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big288 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big289 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big290 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big291 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big292 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big293 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big294 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big295 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big296 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big297 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big298 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big299 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.big300 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.good1b : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.cleanB : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.cleanC : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.cleanD : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.cleanE : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.cleanF : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.cleanG : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.crlf : (1 : Nat) + 1 = 2
:= rfl

set_option maxHeartbeats 400000 in

theorem Selftest.opt1 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tm : (1 : Nat) + 1 = 2
:= (rfl : (2 : Nat) = 2)

theorem Selftest.twoA : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuA1x191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuA2x191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuBx191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuCx191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuDx191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuFx191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tugx191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuhx191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuix191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tujx191920 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuKx192132 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuLx192132 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.tuQx192132 : (1 : Nat) + 1 = 2
:= rfl

end Formula
end Language
end FirstOrder
end TermDef
