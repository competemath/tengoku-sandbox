-- Tengoku.EquationalTheories.ForMathlib.Definability: verified translations of equational_theories/ForMathlib/Definability.lean (4 theorems)
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

end Formula
end Language
end FirstOrder
end TermDef
