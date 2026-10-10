/-
Poisson kernel on the unit circle for JSP-000868 (split from JensenWeight.lean).
-/
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import JSP000868.JensenWeight.Quadratic

open Complex Filter InnerProductSpace Metric Real Set Topology
open scoped ComplexConjugate Topology

noncomputable section

namespace JSP000868
namespace JensenWeight

/-- The Poisson kernel at the real point `r`, as a function on the circle. -/
def poissonKernel (r : ℝ) (z : ℂ) : ℝ :=
  (herglotzRieszKernel 0 (r : ℂ) z).re

/-- Minimum of the Poisson kernel on the unit circle. -/
def kernelLower (r : ℝ) : ℝ := (1 - r) / (1 + r)

/-- Nonnegative weight: Poisson kernel minus its minimum. -/
def weight (r : ℝ) (z : ℂ) : ℝ := poissonKernel r z - kernelLower r

/-- The Poisson kernel averages to 1 over the unit circle. -/
lemma circleAverage_poissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (poissonKernel r) 0 1 = 1 := by
  have hw : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hf : HarmonicContOnCl (fun _ : ℂ ↦ (1 : ℝ)) (ball 0 1) :=
    harmonicContOnCl_const
  have hthm := hf.circleAverage_re_herglotzRieszKernel_smul (w := (r : ℂ)) hw
  -- hthm : circleAverage ((re ∘ herglotzRieszKernel 0 (r:ℂ)) • (fun _ => 1)) 0 1 = 1
  have heq : ((Complex.re ∘ herglotzRieszKernel 0 (r : ℂ)) • (fun _ : ℂ ↦ (1 : ℝ)))
      = poissonKernel r := by
    funext z
    simp [poissonKernel, smul_eq_mul, mul_one, Function.comp_apply]
  rw [heq] at hthm
  exact hthm

/-- The Poisson kernel is continuous on the unit circle. -/
lemma continuousOn_poissonKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (poissonKernel r) (sphere (0 : ℂ) 1) := by
  have hw : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hcont := continuousOn_herglotzRieszKernel_sphere (c := 0) (R := 1) (w := (r:ℂ)) hw
  have hEq : (sphere (0:ℂ) |1|) = sphere (0:ℂ) 1 := by
    congr 1
    norm_num
  rw [hEq] at hcont
  have hcomp := Complex.continuous_re.comp_continuousOn hcont
  have heq : (Complex.re ∘ herglotzRieszKernel 0 (r:ℂ)) = poissonKernel r := by
    funext z
    simp [poissonKernel, Function.comp_apply]
  rw [heq] at hcomp
  exact hcomp

/-- Poisson integral of `log ‖· - a‖` reproduces `log ‖r - a‖` (`‖a‖ = 1`). -/
lemma circleAverage_kernel_mul_log {r : ℝ} {a : ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ‖a‖ = 1) :
    circleAverage (fun w ↦ poissonKernel r w * Real.log ‖w - a‖) 0 1 =
      Real.log ‖(r : ℂ) - a‖ := by
  have heq : (fun w ↦ poissonKernel r w * Real.log ‖w - a‖)
      = (Complex.re ∘ herglotzRieszKernel 0 (r : ℂ)) * (fun w => Real.log ‖w - a‖) := by
    funext w
    simp [poissonKernel, Pi.mul_apply, Function.comp_apply]
  rw [heq]
  apply circleAverage_re_herglotzRieszKernel_mul_log
  · simpa [mem_sphere_iff_norm] using ha
  · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1

/-- The Poisson kernel dominates its minimum on the unit circle. -/
lemma poissonKernel_ge_kernelLower {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    kernelLower r ≤ poissonKernel r z := by
  have hw : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h := le_re_herglotzRieszKernel (c := 0) (R := 1) hz hw
  -- h : (1 - ‖(r:ℂ) - 0‖)/(1 + ‖(r:ℂ) - 0‖) ≤ ((z - 0 + ((r:ℂ)-0))/((z-0)-((r:ℂ)-0))).re
  have hNorm : ‖(r : ℂ) - (0:ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  rw [hNorm] at h
  have hEq : (herglotzRieszKernel 0 (r:ℂ) z).re
      = ((z - 0 + ((r:ℂ) - 0)) / ((z - 0) - ((r:ℂ) - 0))).re := by
    rw [herglotzRieszKernel_def]
  rw [← hEq] at h
  simpa [poissonKernel, kernelLower] using h

/-- The weight is nonnegative on the unit circle. -/
lemma weight_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : 0 ≤ weight r z :=
  sub_nonneg.mpr (poissonKernel_ge_kernelLower hr0 hr1 hz)

/-- Pairing identity: `log ‖r - ρ‖ + log ‖r - conj ρ‖ = log (quadratic r (ρ.re))`. -/
lemma log_norm_sub_add_log_norm_sub_conj {r : ℝ} {a : ℂ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : ‖a‖ = 1) :
    Real.log ‖(r : ℂ) - a‖ + Real.log ‖(r : ℂ) - conj a‖ =
      Real.log (quadratic r a.re) := by
  have h1 : ‖(r : ℂ) - a‖ ≠ 0 := by
    rw [ne_eq, norm_eq_zero, sub_eq_zero]
    intro hcon
    have hcon2 : ‖(r : ℂ)‖ = ‖a‖ := by rw [hcon]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, ha] at hcon2
    linarith [hr1]
  have h2 : ‖(r : ℂ) - conj a‖ ≠ 0 := by
    rw [ne_eq, norm_eq_zero, sub_eq_zero]
    intro hcon
    have hcon2 : ‖(r : ℂ)‖ = ‖conj a‖ := by rw [hcon]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, Complex.norm_conj, ha] at hcon2
    linarith [hr1]
  have ha2 : a.re ^ 2 + a.im ^ 2 = 1 := by
    have e : a.re ^ 2 + a.im ^ 2 = ‖a‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [e, ha, one_pow]
  have hprod : ((r : ℂ) - a) * ((r : ℂ) - conj a) = ((quadratic r a.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [mul_re, sub_re, ofReal_re, conj_re, sub_im, ofReal_im, conj_im,
        zero_sub, neg_mul, mul_neg]
      -- goal: (r - a.re)^2 + a.im^2 = 1 - 2*a.re*r + r^2
      rw [quadratic]; nlinarith [ha2]
    · simp only [mul_im, sub_re, ofReal_re, conj_re, sub_im, ofReal_im, conj_im,
        zero_sub, neg_mul, mul_neg]
      ring
  have hqpos : 0 < quadratic r a.re := by
    apply quadratic_pos hr0 hr1
    calc |a.re| ≤ ‖a‖ := Complex.abs_re_le_norm a
      _ = 1 := ha
  calc Real.log ‖(r : ℂ) - a‖ + Real.log ‖(r : ℂ) - conj a‖
      = Real.log (‖(r : ℂ) - a‖ * ‖(r : ℂ) - conj a‖) := (Real.log_mul h1 h2).symm
    _ = Real.log ‖((r : ℂ) - a) * ((r : ℂ) - conj a)‖ := by rw [norm_mul]
    _ = Real.log (quadratic r a.re) := by
        rw [hprod, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]

end JensenWeight
end JSP000868
