/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!

Puzzle referenced from this tweet: https://twitter.com/sigfpe/status/1474173467016589323

From the book _Out of their Minds: The Lives and Discoveries of 15 Great Computer Scientists_
by Dennis Shasha and Cathy Lazere.

Problem: Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all of them
except perhaps the first one belong to the same class?

-/

namespace KolmogorovStreams
open scoped Stream'

variable {α : Type}

def break_into_words :
   (Stream' ℕ) → -- word lengths
   (Stream' α) → -- original sequence
   (Stream' (List α)) -- sequence of words
 := Function.curry
     (Stream'.corec
       (fun ⟨lengths, a'⟩ ↦ a'.take lengths.head)
       (fun ⟨lengths, a'⟩ ↦ ⟨lengths.tail, a'.drop lengths.head⟩))

/--
Dropping the first word is equivalent to dropping `first_length` symbols of the original stream.
-/
lemma break_into_words_cons
    (lengths : Stream' ℕ)
    (first_length : ℕ)
    (a : Stream' α) :
    (break_into_words (first_length::lengths) a).tail =
           break_into_words lengths (a.drop first_length) := by
  simp [break_into_words, Stream'.corec, Stream'.tail_map, Stream'.tail_iterate]

lemma break_into_words_closed_form
    (lengths : Stream' ℕ)
    (a : Stream' α)
   : break_into_words lengths a =
      (fun i ↦ Stream'.take (lengths i) (Stream'.drop (∑ j ∈ Finset.range i, lengths j) a)) := by
  funext n
  induction n generalizing lengths a with
  | zero => rfl
  | succ n ih =>
    have h1 : (break_into_words lengths a).tail =
        break_into_words lengths.tail (a.drop lengths.head) := by
      conv_lhs => rw [← Stream'.eta lengths]
      exact break_into_words_cons _ _ _
    calc break_into_words lengths a (n + 1)
        = break_into_words lengths.tail (a.drop lengths.head) n := congrFun h1 n
      _ = _ := by
            rw [ih]
            simp [Stream'.drop_drop, Finset.sum_range_succ' (fun j => lengths j), Nat.add_comm]
            rfl

def all_prefixes (p : List α → Prop) (a : Stream' α) : Prop := a.inits.All p

lemma take_prefix
    (is_decent : List α → Prop)
    (a : Stream' α)
    (ha : all_prefixes is_decent a)
    (n : ℕ)
    (hn : 0 < n) : is_decent (a.take n) := by
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n => simpa [Stream'.get_inits] using ha n

lemma not_all_prefixes
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h : ¬ all_prefixes is_decent a) :
    ∃ n, ¬ is_decent (a.take (Nat.succ n)) := by
  simpa [all_prefixes, Stream'.all_def, Stream'.get_inits] using h

/--
If from every "good" position of the stream we can carve off a nonempty word
satisfying `q`, landing at another good position, then the stream can be broken
into words that all satisfy `q`.
-/
lemma exists_break_into_words
    (q : List α → Prop)
    (good : ℕ → Prop)
    (a : Stream' α)
    (h0 : good 0)
    (h : ∀ n, good n → ∃ k, 0 < k ∧ good (n + k) ∧ q ((a.drop n).take k)) :
    ∃ lengths : Stream' ℕ,
      lengths.All (0 < ·) ∧ (break_into_words lengths a).All q := by
  choose k hpos hgood hq using h
  -- iterate the choice, starting at position 0
  let s : ℕ → {n // good n} :=
    fun i ↦ i.rec ⟨0, h0⟩ fun _ p ↦ ⟨p.1 + k p.1 p.2, hgood p.1 p.2⟩
  let lengths : Stream' ℕ := fun i ↦ k (s i).1 (s i).2
  have hs : ∀ i, (s i).1 = ∑ j ∈ Finset.range i, lengths j := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Finset.sum_range_succ, ← ih]
  have hall : (break_into_words lengths a).All q := by
    rw [break_into_words_closed_form]
    intro i
    show q (Stream'.take (lengths i) (Stream'.drop (∑ j ∈ Finset.range i, lengths j) a))
    rw [← hs i]
    exact hq _ _
  exact ⟨lengths, fun i ↦ hpos _ _, hall⟩

def all_same_class
    (is_decent : List α → Prop)
    (b : Stream' (List α))
    : Prop :=
  b.All is_decent ∨ b.All (fun w ↦ ¬is_decent w)

end KolmogorovStreams
