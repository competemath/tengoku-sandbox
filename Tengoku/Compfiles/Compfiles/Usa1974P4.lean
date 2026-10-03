/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom, Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1974, Problem 4

A, B, C play a series of games. Each game is between two players.
The next game is between the winner and the person who was not playing.
The series continues until one player has won two games. He wins the series.
A is the weakest player, C the strongest. Each player has a fixed probability
of winning against a given opponent. A chooses who plays the first game.
Show that he should choose to play himself against B.
-/

namespace Usa1974P4

/-- The three players of the series. -/
inductive Player | A | B | C
  deriving DecidableEq

/-- The player who sits out a game between `x` and `y`.
Only meaningful for `x ≠ y`; returns `A` on the diagonal. -/
def third : Player → Player → Player
  | .A, .B => .C
  | .B, .A => .C
  | .A, .C => .B
  | .C, .A => .B
  | .B, .C => .A
  | .C, .B => .A
  | _, _ => .A

/-- The probability that player `A` wins the series, where

* `win x y` is the probability that `x` beats `y` in a single game,
* the next game is played between `w` (the winner of the previous game)
  and `i` (the player who sat out the previous game); the loser of a game
  sits out the next one,
* `hist` is the list of winners of the games played so far, and
* `n` is a fuel bounding the number of games still to be played.

The series ends as soon as some player has won two games in total, so it
lasts at most four games: if no one has won twice after three games then the
three winners so far are three distinct players, and the fourth game is played
between two of them, so its winner reaches two wins. -/
def probWinA (win : Player → Player → ℝ) :
    ℕ → Player → Player → List Player → ℝ
  | 0, _, _, _ => 0
  | n + 1, w, i, hist =>
      win w i * (if w ∈ hist then (if w = .A then 1 else 0)
                 else probWinA win n w (third w i) (w :: hist)) +
      win i w * (if i ∈ hist then (if i = .A then 1 else 0)
                 else probWinA win n i (third w i) (i :: hist))

/-- The probability that A wins the series when the first game is A against B. -/
def probFirstAB (win : Player → Player → ℝ) : ℝ := probWinA win 4 .A .B []

/-- The probability that A wins the series when the first game is A against C. -/
def probFirstAC (win : Player → Player → ℝ) : ℝ := probWinA win 4 .A .C []

/-- The probability that A wins the series when the first game is B against C. -/
def probFirstBC (win : Player → Player → ℝ) : ℝ := probWinA win 4 .B .C []

/-- Expanding the game tree when the first game is A against B: writing XbY for
"X beats Y", A wins the series exactly via the outcome sequences
AbB · AbC, AbB · CbA · BbC · AbB, and BbA · CbB · AbC · AbB. -/
lemma probFirstAB_eq (win : Player → Player → ℝ)
    (hBA : win .B .A = 1 - win .A .B) (hCA : win .C .A = 1 - win .A .C)
    (hCB : win .C .B = 1 - win .B .C) :
    probFirstAB win =
      win .A .B * win .A .C + win .A .B * (1 - win .A .C) * win .B .C * win .A .B +
        (1 - win .A .B) * (1 - win .B .C) * win .A .C * win .A .B := by
  simp [probFirstAB, probWinA, third, hBA, hCA, hCB]
  ring

/-- Expanding the game tree when the first game is A against C: A wins the series
exactly via the outcome sequences AbC · AbB, AbC · BbA · CbB · AbC, and
CbA · BbC · AbB · AbC. -/
lemma probFirstAC_eq (win : Player → Player → ℝ)
    (hBA : win .B .A = 1 - win .A .B) (hCA : win .C .A = 1 - win .A .C)
    (hCB : win .C .B = 1 - win .B .C) :
    probFirstAC win =
      win .A .C * win .A .B + win .A .C * (1 - win .A .B) * (1 - win .B .C) * win .A .C +
        (1 - win .A .C) * win .B .C * win .A .B * win .A .C := by
  simp [probFirstAC, probWinA, third, hBA, hCA, hCB]
  ring

/-- Expanding the game tree when the first game is B against C: A wins the series
exactly via the outcome sequences BbC · AbB · AbC and CbB · AbC · AbB. -/
lemma probFirstBC_eq (win : Player → Player → ℝ)
    (hBA : win .B .A = 1 - win .A .B) (hCA : win .C .A = 1 - win .A .C)
    (hCB : win .C .B = 1 - win .B .C) :
    probFirstBC win =
      win .B .C * win .A .B * win .A .C + (1 - win .B .C) * win .A .C * win .A .B := by
  simp [probFirstBC, probWinA, third, hBA, hCA, hCB]
  ring

end Usa1974P4
