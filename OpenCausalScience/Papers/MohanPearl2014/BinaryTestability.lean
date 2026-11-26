module
public import Std

/-! Mohan and Pearl (2014), Theorem 3 and Table 2.
For fully observed binary X and partially observed binary Y, two interval
bounds on the common marginal of Y express the completion criterion. -/

namespace OpenCausalScience.Papers.MohanPearl2014.BinaryTestability

@[expose] public section

/-- Observed cell masses in a fixed stratum of X. Missing values of Y
are coded by a single proxy symbol. -/
structure ManifestRow where
  seenZero : Rat
  seenOne : Rat
  missing : Rat

def ManifestRow.total (row : ManifestRow) : Rat :=
  row.seenZero + row.seenOne + row.missing

def ManifestRow.lower (row : ManifestRow) : Rat := row.seenZero / row.total
def ManifestRow.upper (row : ManifestRow) : Rat := (row.seenZero + row.missing) / row.total

/-- The part missingZero of the missing mass is assigned to Y=0.
The other part, missing - missingZero, is assigned to Y=1. -/
def HasCompletedRate (row : ManifestRow) (rate : Rat) : Prop :=
  ∃ missingZero : Rat, 0 ≤ missingZero ∧ missingZero ≤ row.missing ∧
    row.seenZero + missingZero = rate * row.total

theorem completed_rate_iff_interval (row : ManifestRow) (rate : Rat)
    (supported : 0 < row.total) :
    HasCompletedRate row rate ↔ row.lower ≤ rate ∧ rate ≤ row.upper := by
  have nonzero : row.total ≠ 0 := by
    intro h
    rw [h] at supported
    exact Rat.lt_irrefl supported
  have lowerCancel : row.lower * row.total = row.seenZero := Rat.div_mul_cancel nonzero
  have upperCancel : row.upper * row.total = row.seenZero + row.missing :=
    Rat.div_mul_cancel nonzero
  constructor
  · rintro ⟨m, h₀, h₁, assignment⟩
    constructor
    · apply Rat.le_of_mul_le_mul_right _ supported
      rw [lowerCancel, ← assignment]
      grind
    · apply Rat.le_of_mul_le_mul_right _ supported
      rw [upperCancel, ← assignment]
      grind
  · rintro ⟨lower, upper⟩
    have low := Rat.mul_le_mul_of_nonneg_left lower (Rat.le_of_lt supported)
    have high := Rat.mul_le_mul_of_nonneg_left upper (Rat.le_of_lt supported)
    rw [Rat.mul_comm row.total row.lower, lowerCancel, Rat.mul_comm row.total rate] at low
    rw [Rat.mul_comm row.total row.upper, upperCancel, Rat.mul_comm row.total rate] at high
    refine ⟨rate * row.total - row.seenZero, ?_, ?_, ?_⟩ <;> grind

/-- The two completed conditional rates of Y=0 coincide exactly when
the binary completion satisfies X ⟂ Y. -/
def AllowsIndependence (first second : ManifestRow) : Prop :=
  ∃ rate, HasCompletedRate first rate ∧ HasCompletedRate second rate

theorem allows_independence_iff_overlap (first second : ManifestRow)
    (firstSupported : 0 < first.total) (secondSupported : 0 < second.total)
    (firstMissing : 0 ≤ first.missing) (secondMissing : 0 ≤ second.missing) :
    AllowsIndependence first second ↔ first.lower ≤ second.upper ∧ second.lower ≤ first.upper := by
  have firstNonempty : first.lower ≤ first.upper :=
    (completed_rate_iff_interval first first.lower firstSupported).mp
      ⟨0, by simp, firstMissing, by
        change first.seenZero + 0 = first.seenZero / first.total * first.total
        rw [Rat.div_mul_cancel (by grind), Rat.add_zero]⟩ |>.2
  have secondNonempty : second.lower ≤ second.upper :=
    (completed_rate_iff_interval second second.lower secondSupported).mp
      ⟨0, by simp, secondMissing, by
        change second.seenZero + 0 = second.seenZero / second.total * second.total
        rw [Rat.div_mul_cancel (by grind), Rat.add_zero]⟩ |>.2
  constructor
  · rintro ⟨rate, h₀, h₁⟩
    obtain ⟨firstLow, firstHigh⟩ := (completed_rate_iff_interval first rate firstSupported).mp h₀
    obtain ⟨secondLow, secondHigh⟩ := (completed_rate_iff_interval second rate secondSupported).mp h₁
    exact ⟨Rat.le_trans firstLow secondHigh, Rat.le_trans secondLow firstHigh⟩
  · rintro ⟨firstToSecond, secondToFirst⟩
    by_cases order : first.lower ≤ second.lower
    · refine ⟨second.lower, (completed_rate_iff_interval first _ firstSupported).mpr
        ⟨order, secondToFirst⟩, (completed_rate_iff_interval second _ secondSupported).mpr
        ⟨Rat.le_refl, secondNonempty⟩⟩
    · have reverse : second.lower ≤ first.lower := by grind
      refine ⟨first.lower, (completed_rate_iff_interval first _ firstSupported).mpr
        ⟨Rat.le_refl, firstNonempty⟩, (completed_rate_iff_interval second _ secondSupported).mpr
        ⟨reverse, firstToSecond⟩⟩

def table2P1False : ManifestRow := ⟨8/81, 6/81, 20/81⟩
def table2P1True : ManifestRow := ⟨4/81, 3/81, 40/81⟩
def table2P2False : ManifestRow := ⟨13/41, 11/41, 3/41⟩
def table2P2True : ManifestRow := ⟨7/41, 5/41, 2/41⟩
def table2P3False : ManifestRow := ⟨100/125, 5/125, 5/125⟩
def table2P3True : ManifestRow := ⟨7/125, 3/125, 5/125⟩

theorem table2_p1_allows_independence : AllowsIndependence table2P1False table2P1True := by
  rw [allows_independence_iff_overlap]
  all_goals decide +kernel

theorem table2_p2_allows_independence : AllowsIndependence table2P2False table2P2True := by
  rw [allows_independence_iff_overlap]
  all_goals decide +kernel

theorem table2_p3_refutes_independence : ¬ AllowsIndependence table2P3False table2P3True := by
  rw [allows_independence_iff_overlap]
  all_goals decide +kernel

end
end OpenCausalScience.Papers.MohanPearl2014.BinaryTestability
