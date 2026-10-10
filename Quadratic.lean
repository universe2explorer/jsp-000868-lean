/-
Quadratic helper for JSP-000868 (split from JensenWeight.lean).
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Abs

open Complex Filter Metric Real Set Topology
open scoped ComplexConjugate Topology

noncomputable section

namespace JSP000868
namespace JensenWeight

/-- The quadratic `1 - 2*t*r + r^2 = ‖r - (t + i√(1-t²))‖^2`. -/
def quadratic (r t : ℝ) : ℝ := 1 - 2 * t * r + r ^ 2

lemma quadratic_pos {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : |t| ≤ 1) :
    0 < quadratic r t := by
  rw [abs_le] at ht
  have h : quadratic r t = (1 - r) ^ 2 + 2 * r * (1 - t) := by
    simp [quadratic]; ring
  rw [h]
  have h1 : (0 : ℝ) < (1 - r) ^ 2 := by
    apply sq_pos_of_ne_zero
    · -- `1 - r ≠ 0`
      intro hcon
      have : (1 : ℝ) = r := by linarith
      linarith
  have h2 : (0 : ℝ) ≤ 2 * r * (1 - t) := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num) hr0
    · linarith [ht.2]
  linarith

end JensenWeight
end JSP000868
