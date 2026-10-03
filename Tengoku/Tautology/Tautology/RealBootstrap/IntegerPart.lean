import Tengoku.Tautology.Tautology.RealBootstrap.RationalDensity

/-!
# The integer part and the fractional part

The floor of a field element as an internal integer, with the two properties
that characterise it -- it is at most the element, and adding one overshoots --
and the fractional part as the difference, lying in the unit interval.

Uniqueness is what makes `integerFloor` a function rather than a choice: no
internal integer lies strictly between zero and one
(`Tautology.RealBootstrap.InternalInt`), so two candidate floors of the same
element coincide. Existence comes from the ceiling statement of
`Tautology.RealBootstrap.RationalDensity`, and hence from the Archimedean
property.

## Position and role

Implementation module at complete-field level, the top of the internal-number
strand of the region.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- Every element has an internal-integer floor: some z with
z <= a < z + 1. It is derived from the ceiling theorem one unit below; the
witness is unique by `internalInt_floor_unique`, and `integerFloor` below
turns it into a function. -/
theorem exists_internalInt_floor (a : alpha) :
    Exists (fun z : alpha =>
      And (IsOrderedFieldBaseLike.InternalInt C.field z)
        (And (C.field.le z a)
          (C.field.lt a (C.field.add z C.field.one)))) := by
  let F := C.field
  cases exists_internalInt_ceiling C (F.sub a F.one) with
  | intro z hz =>
      have hsub_add_one :
          F.add (F.sub a F.one) F.one = a :=
        IsOrderedFieldBaseLike.sub_add_cancel F a F.one
      have hz_le_a : F.le z a := by
        have hceil : F.le z (F.add (F.sub a F.one) F.one) := hz.right.left
        rwa [hsub_add_one] at hceil
      have ha_lt_z_one : F.lt a (F.add z F.one) := by
        have h := IsOrderedFieldBaseLike.add_lt_add_right F
          hz.right.right F.one
        rwa [hsub_add_one] at h
      exact Exists.intro z
        (And.intro hz.left (And.intro hz_le_a ha_lt_z_one))

/-- Two internal integers can both satisfy the floor bounds only by
coinciding. Distinct internal integers are a full unit apart -- their
difference is internal and cannot lie strictly between zero and one -- so
the unit-wide window `z <= a < z + 1` has room for exactly one of them. -/
theorem internalInt_floor_unique {a z w : alpha}
    (hz :
      And (IsOrderedFieldBaseLike.InternalInt C.field z)
        (And (C.field.le z a)
          (C.field.lt a (C.field.add z C.field.one))))
    (hw :
      And (IsOrderedFieldBaseLike.InternalInt C.field w)
        (And (C.field.le w a)
          (C.field.lt a (C.field.add w C.field.one)))) :
    z = w := by
  let F := C.field
  have hzw : F.le z w := by
    apply IsOrderedFieldBaseLike.le_of_not_lt F
    intro hwz
    have hpos : F.lt F.zero (F.sub z w) :=
      IsOrderedFieldBaseLike.sub_pos_of_lt F hwz
    have hz_lt_w_one : F.lt z (F.add w F.one) :=
      F.lt_of_le_of_lt hz.right.left hw.right.right
    have hlt_one : F.lt (F.sub z w) F.one :=
      IsOrderedFieldBaseLike.sub_lt_of_lt_add F hz_lt_w_one
    exact
      (IsOrderedFieldBaseLike.not_internalInt_of_zero_lt_of_lt_one
        F hpos hlt_one)
        (IsOrderedFieldBaseLike.internalInt_sub F hz.left hw.left)
  have hwz : F.le w z := by
    apply IsOrderedFieldBaseLike.le_of_not_lt F
    intro hzw'
    have hpos : F.lt F.zero (F.sub w z) :=
      IsOrderedFieldBaseLike.sub_pos_of_lt F hzw'
    have hw_lt_z_one : F.lt w (F.add z F.one) :=
      F.lt_of_le_of_lt hw.right.left hz.right.right
    have hlt_one : F.lt (F.sub w z) F.one :=
      IsOrderedFieldBaseLike.sub_lt_of_lt_add F hw_lt_z_one
    exact
      (IsOrderedFieldBaseLike.not_internalInt_of_zero_lt_of_lt_one
        F hpos hlt_one)
        (IsOrderedFieldBaseLike.internalInt_sub F hw.left hz.left)
  exact F.le_antisymm hzw hwz

/-- The floor function: the witness of `exists_internalInt_floor`, extracted
by classical choice. The three lemmas that follow are its interface, and
`integerFloor_eq_of_internalInt_bounds` recognizes the value from any
internal integer meeting the same bounds. -/
noncomputable def integerFloor (a : alpha) : alpha :=
  Classical.choose (exists_internalInt_floor C a)

theorem integerFloor_internalInt (a : alpha) :
    IsOrderedFieldBaseLike.InternalInt C.field (integerFloor C a) :=
  (Classical.choose_spec (exists_internalInt_floor C a)).left

theorem integerFloor_le (a : alpha) :
    C.field.le (integerFloor C a) a :=
  (Classical.choose_spec (exists_internalInt_floor C a)).right.left

theorem lt_integerFloor_add_one (a : alpha) :
    C.field.lt a (C.field.add (integerFloor C a) C.field.one) :=
  (Classical.choose_spec (exists_internalInt_floor C a)).right.right

theorem integerFloor_eq_of_internalInt_bounds {a z : alpha}
    (hz : IsOrderedFieldBaseLike.InternalInt C.field z)
    (hza : C.field.le z a)
    (haz : C.field.lt a (C.field.add z C.field.one)) :
    integerFloor C a = z :=
  internalInt_floor_unique C
    (And.intro (integerFloor_internalInt C a)
      (And.intro (integerFloor_le C a)
        (lt_integerFloor_add_one C a)))
    (And.intro hz (And.intro hza haz))

/-- The fractional part, the difference between an element and its floor. It
lands in `[0, 1)` by the two lemmas below and is unchanged by adding an
internal integer. -/
noncomputable def fractionalPart (a : alpha) : alpha :=
  C.field.sub a (integerFloor C a)

theorem fractionalPart_nonneg (a : alpha) :
    C.field.le C.field.zero (fractionalPart C a) := by
  unfold fractionalPart
  exact IsOrderedFieldBaseLike.sub_nonneg_of_le C.field
    (integerFloor_le C a)

theorem fractionalPart_lt_one (a : alpha) :
    C.field.lt (fractionalPart C a) C.field.one := by
  unfold fractionalPart
  exact IsOrderedFieldBaseLike.sub_lt_of_lt_add C.field
    (lt_integerFloor_add_one C a)

theorem fractionalPart_eq_sub_of_internalInt_bounds {a z : alpha}
    (hz : IsOrderedFieldBaseLike.InternalInt C.field z)
    (hza : C.field.le z a)
    (haz : C.field.lt a (C.field.add z C.field.one)) :
    fractionalPart C a = C.field.sub a z := by
  unfold fractionalPart
  rw [integerFloor_eq_of_internalInt_bounds C hz hza haz]

theorem fractionalPart_internalInt {a : alpha}
    (ha : IsOrderedFieldBaseLike.InternalInt C.field a) :
    fractionalPart C a = C.field.zero := by
  let F := C.field
  have ha_lt_add_one : F.lt a (F.add a F.one) := by
    have h := IsOrderedFieldBaseLike.add_lt_add_left F
      (IsOrderedFieldBaseLike.zero_lt_one F) a
    rwa [F.add_zero] at h
  rw [fractionalPart_eq_sub_of_internalInt_bounds C
    ha (F.le_refl a) ha_lt_add_one]
  exact F.sub_self a

theorem fractionalPart_add_internalInt {a z : alpha}
    (hz : IsOrderedFieldBaseLike.InternalInt C.field z) :
    fractionalPart C (C.field.add a z) = fractionalPart C a := by
  let F := C.field
  have hfloor :
      integerFloor C (F.add a z) = F.add (integerFloor C a) z := by
    apply integerFloor_eq_of_internalInt_bounds C
    · exact IsOrderedFieldBaseLike.internalInt_add F
        (integerFloor_internalInt C a) hz
    · exact F.add_le_add_right (integerFloor_le C a) z
    · have h := F.add_lt_add_right (lt_integerFloor_add_one C a) z
      rw [F.add_assoc, F.add_comm F.one z, <- F.add_assoc] at h
      exact h
  unfold fractionalPart
  rw [hfloor]
  rw [IsOrderedFieldBaseLike.add_sub_add_eq_sub_add_sub F]
  rw [F.sub_self, F.add_zero]

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
