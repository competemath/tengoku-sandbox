/-
Copyright (c) 2026 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1994, Problem 6

Show that there exists a set A of positive integers with the following
property: For any infinite set S of primes there exist two positive integers
m ∈ A and n ∉ A each of which is a product of k distinct elements of S for
some k ≥ 2.

-/

namespace Imo1994P6

def IsProductOfkDistinctMembers (x : ℕ) (k : ℕ) (S : Set ℕ) : Prop :=
  ∃ S' : Finset S, S'.card = k ∧ x = ∏ p ∈ S', p.val

def Primes := { p : ℕ | p.Prime }
instance : Infinite Primes := Nat.infinite_setOfPred_prime.to_subtype
noncomputable def primes_iso : ℕ ≃o ↑Primes := Nat.Subtype.orderIsoOfNat Primes

-- Number of distinct prime factors of x
def ω : ℕ → ℕ := fun x ↦ (Nat.primeFactors x).card

lemma prod_of_primes {S : Set ℕ} {S' : Finset S} (h : ∀p ∈ S, p.Prime) :
  (∏ p ∈ S', p.val).primeFactors = S'.map ⟨Subtype.val, Subtype.val_injective⟩ := by
  have : ∏ p ∈ S', p.val = ∏ p ∈ S'.map ⟨Subtype.val, Subtype.val_injective⟩, p :=
    Eq.symm (Finset.prod_map S' { toFun := Subtype.val, inj' := Subtype.val_injective } fun x ↦ x)
  rw [this, Nat.primeFactors_prod]
  aesop

lemma minFac_prod_primes {S : Set ℕ} (k i : ℕ) (f : ℕ ≃o S)
    (hS : ∀ s ∈ S, s.Prime) (hk : 0 < k) :
    (∏ p ∈ (Finset.range k).image (fun j ↦ f (j + i)), (p : ℕ)).minFac = (f i).val := by
  set Sf := (Finset.range k).image (fun j ↦ f (j + i))
  have hfi_mem : f i ∈ Sf :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, by simp⟩
  have hfi_prime : ((f i) : ℕ).Prime := hS _ (f i).prop
  have hprod_ne_one : ∏ p ∈ Sf, (p : ℕ) ≠ 1 := by
    intro h
    exact absurd ((Finset.prod_eq_one_iff_of_one_le'
      (fun x hx ↦ (hS x.val x.prop).one_le)).mp h _ hfi_mem) hfi_prime.one_lt.ne'
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hfi_prime.two_le (Finset.dvd_prod_of_mem _ hfi_mem)
  · -- minFac is prime and divides the product, so it divides some prime factor
    have hmf_prime := Nat.minFac_prime hprod_ne_one
    obtain ⟨a, ha_mem, hmf_dvd_a⟩ :=
      (hmf_prime.prime.dvd_finsetProd_iff _).mp (Nat.minFac_dvd _)
    -- Since both minFac and a.val are prime, minFac = a.val
    have : (∏ p ∈ Sf, (p : ℕ)).minFac = a.val := by
      cases (hS a.val a.prop).eq_one_or_self_of_dvd _ hmf_dvd_a with
      | inl h => exact absurd h hmf_prime.one_lt.ne'
      | inr h => exact h
    -- And a = f(j+i) for some j ≥ 0, so a.val ≥ (f i).val
    rw [this]
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha_mem
    exact (f.monotone (Nat.le_add_left i j))

lemma prod_of_distinct_members (k i : ℕ) (S : Set ℕ) (f : ℕ ≃o S) : IsProductOfkDistinctMembers (∏ p ∈ ((Finset.range k).image (fun j ↦ f (j+i))), p) k S := by
  unfold IsProductOfkDistinctMembers
  let Sₘ := (Finset.range k).image (fun j ↦ f (j+i))
  let m : ℕ := ∏ p ∈ Sₘ, p
  use Sₘ
  have hinj : (fun j ↦ (f (j + i))).Injective := by grind only [Function.not_injective_iff, OrderIso.apply_eq_iff_eq]
  have : Sₘ.card = k := by
    unfold Sₘ
    rw [Finset.card_image_of_injective (Finset.range k) hinj]
    grind
  exact ⟨this, rfl⟩

lemma primeFactors_card  {S : Set ℕ} (k i : ℕ) (f : ℕ ≃o S) (h : ∀ s ∈ S, s.Prime) : ω (∏ p ∈ ((Finset.range k).image (fun j ↦ f (j+i))), p) = k := by
  let Sₙ := (Finset.range k).image (fun j ↦ f (j+i))
  let n : ℕ := ∏ p ∈ Sₙ, p
  unfold ω
  rw [prod_of_primes h]
  simp
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range k
  · exact fun _ _ h => Nat.add_right_cancel (f.injective h)

end Imo1994P6
