/-
Log-boundary function and exceptional set for JSP-000868 (split from JensenWeight.lean).
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Complex.Basic

open Complex Filter Metric Real Set Topology
open scoped ComplexConjugate Topology
open Classical

noncomputable section

namespace JSP000868
namespace JensenWeight

/-- Boundary log-potential whose circle average is `n * log (h/2)`. -/
def logBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) (z : ℂ) : ℝ :=
  n * Real.log (h / 2) + ∑ i, (Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)

/-- `logBoundary` is circle-integrable (logarithmic singularities are integrable). -/
lemma circleIntegrable_logBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) :
    CircleIntegrable (logBoundary h ρ) 0 1 := by
  have e : logBoundary h ρ = (fun _ : ℂ => n * Real.log (h / 2)) +
      ∑ i : Fin n, (fun z : ℂ => Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖) := by
    funext z
    simp [logBoundary, Finset.sum_apply]
  rw [e]
  apply CircleIntegrable.add (circleIntegrable_const _ _ _)
  apply CircleIntegrable.sum Finset.univ
  intro i _
  exact CircleIntegrable.add (circleIntegrable_log_norm_sub_const 1)
    (circleIntegrable_log_norm_sub_const 1)

/-- The unweighted circle average of `logBoundary` is `n * log (h/2)`. -/
lemma circleAverage_logBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ)
    (hρ : ∀ i, ‖ρ i‖ = 1) :
    circleAverage (logBoundary h ρ) 0 1 = n * Real.log (h / 2) := by
  have e : logBoundary h ρ =
      (fun _ : ℂ => n * Real.log (h / 2)) +
        ∑ i : Fin n, (fun z : ℂ => Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖) := by
    funext z
    simp [logBoundary]
  have hconst : CircleIntegrable (fun _ : ℂ => n * Real.log (h / 2)) 0 1 :=
    circleIntegrable_const _ _ _
  have hsum : CircleIntegrable
      (∑ i : Fin n, (fun z : ℂ => Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)) 0 1 := by
    apply CircleIntegrable.sum Finset.univ
    intro i _
    exact CircleIntegrable.add (circleIntegrable_log_norm_sub_const 1)
      (circleIntegrable_log_norm_sub_const 1)
  have hz : ∀ i : Fin n,
      circleAverage (fun z : ℂ => Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖) 0 1
        = 0 := by
    intro i
    have h1 : CircleIntegrable (fun z : ℂ => Real.log ‖z - ρ i‖) 0 1 :=
      circleIntegrable_log_norm_sub_const 1
    have h2 : CircleIntegrable (fun z : ℂ => Real.log ‖z - conj (ρ i)‖) 0 1 :=
      circleIntegrable_log_norm_sub_const 1
    have e12 : (fun z : ℂ => Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)
        = (fun z : ℂ => Real.log ‖z - ρ i‖) + (fun z : ℂ => Real.log ‖z - conj (ρ i)‖) := by
      funext z; simp [Pi.add_apply]
    rw [e12, circleAverage_add h1 h2,
      circleAverage_log_norm_sub_const₁ (hρ i),
      circleAverage_log_norm_sub_const₁ (by simpa using hρ i),
      add_zero]
  have hsum_avg : circleAverage
      (∑ i : Fin n, (fun z : ℂ => Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)) 0 1
        = 0 := by
    have h := circleAverage_sum (c := (0:ℂ)) (R := (1:ℝ)) (s := Finset.univ)
      (f := fun i (z : ℂ) => Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)
      (fun i _ =>
        CircleIntegrable.add (circleIntegrable_log_norm_sub_const 1)
          (circleIntegrable_log_norm_sub_const 1))
    rw [h]
    simp_rw [hz]
    simp
  rw [e, circleAverage_add hconst hsum, circleAverage_const, hsum_avg, add_zero]

/-- Points where `z` hits a lift or its conjugate (finite exceptional set). -/
def exceptional {n : ℕ} (ρ : Fin n → ℂ) : Set ℂ :=
  Set.range ρ ∪ Set.range (fun i ↦ conj (ρ i))

lemma exceptional_finite {n : ℕ} (ρ : Fin n → ℂ) : (exceptional ρ).Finite :=
  (Set.finite_range ρ).union (Set.finite_range _)

/-- On the unit circle, equal real parts force `z = ρ` or `z = conj ρ`. -/
lemma eq_or_eq_conj_of_re_eq_of_norm_eq_one {z ρ : ℂ}
    (hz : ‖z‖ = 1) (hρ : ‖ρ‖ = 1) (hre : z.re = ρ.re) :
    z = ρ ∨ z = conj ρ := by
  have ez : z.re ^ 2 + z.im ^ 2 = 1 := by
    have e : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [e, hz, one_pow]
  have er : ρ.re ^ 2 + ρ.im ^ 2 = 1 := by
    have e : ρ.re ^ 2 + ρ.im ^ 2 = ‖ρ‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [e, hρ, one_pow]
  have him : z.im ^ 2 = ρ.im ^ 2 := by
    have hsq : z.re ^ 2 = ρ.re ^ 2 := by rw [hre]
    linarith [ez, er, hsq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with h | h
  · left; exact Complex.ext hre h
  · right
    apply Complex.ext
    · simp [hre]
    · simp [h]

/-- Off the exceptional set, real parts are distinct. -/
lemma re_ne_of_notMem_exceptional {n : ℕ} {ρ : Fin n → ℂ} {z : ℂ}
    (hz : ‖z‖ = 1) (hρ : ∀ i, ‖ρ i‖ = 1) (hex : z ∉ exceptional ρ) (i : Fin n) :
    z.re ≠ (ρ i).re := by
  intro hre
  rcases eq_or_eq_conj_of_re_eq_of_norm_eq_one hz (hρ i) hre with h | h
  · exact hex (Or.inl ⟨i, h.symm⟩)
  · exact hex (Or.inr ⟨i, h.symm⟩)

/-- Norm pairing identity on the unit circle. -/
lemma norm_mul_sub_conj {z ρ : ℂ} (hz : ‖z‖ = 1) (hρ : ‖ρ‖ = 1) :
    ‖z - ρ‖ * ‖z - conj ρ‖ = 2 * |z.re - ρ.re| := by
  have ez : z.re ^ 2 + z.im ^ 2 = 1 := by
    have e : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [e, hz, one_pow]
  have er : ρ.re ^ 2 + ρ.im ^ 2 = 1 := by
    have e : ρ.re ^ 2 + ρ.im ^ 2 = ‖ρ‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [e, hρ, one_pow]
  have hsq : (‖z - ρ‖ * ‖z - conj ρ‖) ^ 2 = (2 * |z.re - ρ.re|) ^ 2 := by
    have e1 : ‖z - ρ‖ ^ 2 = (z.re - ρ.re) ^ 2 + (z.im - ρ.im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sub_re, sub_im]; ring
    have e2 : ‖z - conj ρ‖ ^ 2 = (z.re - ρ.re) ^ 2 + (z.im + ρ.im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sub_re, sub_im, conj_re, conj_im]; ring
    rw [mul_pow, e1, e2, mul_pow, sq_abs]
    -- Key algebraic identity, using `ez`, `er`.
    have key : ((z.re - ρ.re)^2 + (z.im - ρ.im)^2) * ((z.re - ρ.re)^2 + (z.im + ρ.im)^2)
        = 4 * (z.re - ρ.re)^2 := by
      have h1 : (z.im - ρ.im)^2 + (z.im + ρ.im)^2 = 2 * (z.im^2 + ρ.im^2) := by ring
      have h2 : (z.im - ρ.im)^2 * (z.im + ρ.im)^2 = (z.im^2 - ρ.im^2)^2 := by ring
      nlinarith [ez, er, h1, h2, sq_nonneg (z.re - ρ.re), sq_nonneg (z.im^2 - ρ.im^2)]
    linarith [key]
  have hnn1 : (0 : ℝ) ≤ ‖z - ρ‖ * ‖z - conj ρ‖ := by positivity
  have hnn2 : (0 : ℝ) ≤ 2 * |z.re - ρ.re| := by positivity
  have hsqrt := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq hnn1, Real.sqrt_sq hnn2] at hsqrt
  exact hsqrt

/-- `logBoundary ≤ 0` on the circle, away from the exceptional set. -/
lemma logBoundary_nonpos {n : ℕ} {h : ℝ} (hh : 0 < h) (ρ : Fin n → ℂ)
    (hρ : ∀ i, ‖ρ i‖ = 1)
    (hbound : ∀ z ∈ sphere (0:ℂ) 1, h^n * ∏ i, |z.re - (ρ i).re| ≤ 1)
    {z : ℂ} (hz : z ∈ sphere (0:ℂ) 1) (hex : z ∉ exceptional ρ) :
    logBoundary h ρ z ≤ 0 := by
  have hzn : ‖z‖ = 1 := by simpa [mem_sphere_iff_norm] using hz
  have hre : ∀ i, z.re ≠ (ρ i).re :=
    fun i => re_ne_of_notMem_exceptional hzn hρ hex i
  have hpos : ∀ i, 0 < |z.re - (ρ i).re| :=
    fun i => abs_pos.mpr (sub_ne_zero.mpr (hre i))
  have hpair : ∀ i, Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖ =
      Real.log (2 * |z.re - (ρ i).re|) := by
    intro i
    have n1 : ‖z - ρ i‖ ≠ 0 := by
      rw [ne_eq, norm_eq_zero, sub_eq_zero]; intro hcon
      exact hex (Or.inl ⟨i, hcon.symm⟩)
    have n2 : ‖z - conj (ρ i)‖ ≠ 0 := by
      rw [ne_eq, norm_eq_zero, sub_eq_zero]; intro hcon
      exact hex (Or.inr ⟨i, hcon.symm⟩)
    rw [← Real.log_mul n1 n2, norm_mul_sub_conj hzn (hρ i)]
  have hprod_pos : 0 < ∏ i, |z.re - (ρ i).re| :=
    Finset.prod_pos (fun i _ => hpos i)
  have hpow_pos : 0 < h ^ n := pow_pos hh n
  -- Rewrite logBoundary as a single log.
  have hLB : logBoundary h ρ z = Real.log (h^n * ∏ i, |z.re - (ρ i).re|) := by
    have e1 : logBoundary h ρ z =
        n * Real.log (h/2) + ∑ i, Real.log (2 * |z.re - (ρ i).re|) := by
      simp only [logBoundary]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact hpair i
    have e2 : Real.log (h^n * ∏ i, |z.re - (ρ i).re|) =
        n * Real.log (h/2) + ∑ i, Real.log (2 * |z.re - (ρ i).re|) := by
      rw [Real.log_mul (ne_of_gt hpow_pos) (ne_of_gt hprod_pos),
        Real.log_pow, log_prod (fun i _ => ne_of_gt (hpos i))]
      -- n * log h = n * log(h/2) + n * log 2
      have e3 : ∀ i : Fin n, Real.log (2 * |z.re - (ρ i).re|) =
          Real.log 2 + Real.log |z.re - (ρ i).re| :=
        fun i => Real.log_mul (by norm_num) (ne_of_gt (hpos i))
      rw [Finset.sum_congr rfl (fun i _ => e3 i)]
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, nsmul_eq_mul]
      rw [Real.log_div (ne_of_gt hh) (by norm_num : (2:ℝ) ≠ 0)]
      ring
    rw [e1, e2]
  rw [hLB]
  have hb := hbound z hz
  have : Real.log (h^n * ∏ i, |z.re - (ρ i).re|) ≤ Real.log 1 :=
    Real.log_le_log (by positivity) hb
  simpa using this

/-- Modified boundary function: zero on the exceptional set. -/
def modifiedLogBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) (z : ℂ) : ℝ :=
  if z ∈ exceptional ρ then 0 else logBoundary h ρ z

lemma modifiedLogBoundary_nonpos {n : ℕ} {h : ℝ} (hh : 0 < h) (ρ : Fin n → ℂ)
    (hρ : ∀ i, ‖ρ i‖ = 1)
    (hbound : ∀ z ∈ sphere (0:ℂ) 1, h^n * ∏ i, |z.re - (ρ i).re| ≤ 1)
    {z : ℂ} (hz : z ∈ sphere (0:ℂ) 1) :
    modifiedLogBoundary h ρ z ≤ 0 := by
  unfold modifiedLogBoundary
  split_ifs with he
  · exact le_refl 0
  · exact logBoundary_nonpos hh ρ hρ hbound hz he

/-- Agreement of the modified and original boundary functions off the exceptional set. -/
lemma modifiedLogBoundary_eventuallyEq {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) :
    modifiedLogBoundary h ρ =ᶠ[codiscreteWithin (sphere (0:ℂ) |1|)] logBoundary h ρ := by
  filter_upwards [compl_finite_mem_codiscreteWithin (exceptional_finite ρ)] with z hz
  simp only [Set.mem_compl_iff] at hz
  unfold modifiedLogBoundary
  rw [if_neg hz]

end JensenWeight
end JSP000868
