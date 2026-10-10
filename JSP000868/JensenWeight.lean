/-
Weighted Jensen estimate for JSP-000868 (Pommerenke's argument).
See JensenWeight/Quadratic.lean, JensenWeight/PoissonKernel.lean,
JensenWeight/LogBoundary.lean for the supporting modules.
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.DiscreteSubset
import JSP000868.JensenWeight.Quadratic
import JSP000868.JensenWeight.PoissonKernel
import JSP000868.JensenWeight.LogBoundary

open Complex Filter Metric Real Set Topology
open scoped ComplexConjugate Topology

noncomputable section

namespace JSP000868
namespace JensenWeight

/-- The weighted average of `logBoundary`: Poisson part yields quadratic logs. -/
lemma circleAverage_weight_mul_logBoundary {n : ℕ} {r h : ℝ} (ρ : Fin n → ℂ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hρ : ∀ i, ‖ρ i‖ = 1) :
    circleAverage (fun z ↦ weight r z * logBoundary h ρ z) 0 1 =
      (1 - kernelLower r) * (n * Real.log (h / 2)) +
        ∑ i, Real.log (quadratic r (ρ i).re) := by
  have hk := continuousOn_poissonKernel hr0 hr1
  have hk' : ContinuousOn (poissonKernel r) (sphere (0:ℂ) |1|) := by simpa using hk
  have hL := circleIntegrable_logBoundary h ρ
  -- Split weight = kernel - kernelLower.
  have hsplit : (fun z ↦ weight r z * logBoundary h ρ z) =
      (fun z ↦ poissonKernel r z * logBoundary h ρ z) -
        (fun z ↦ kernelLower r * logBoundary h ρ z) := by
    funext z; simp [weight]; ring
  have hkL : CircleIntegrable (fun z ↦ poissonKernel r z * logBoundary h ρ z) 0 1 :=
    hL.continuousOn_mul hk'
  have hcL : CircleIntegrable (fun z ↦ kernelLower r * logBoundary h ρ z) 0 1 := by
    have e : (fun z ↦ kernelLower r * logBoundary h ρ z) = (kernelLower r • logBoundary h ρ) := by
      funext z; simp [Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact hL.const_smul
  rw [hsplit, circleAverage_sub hkL hcL]
  -- Second term: kernelLower * average(logBoundary).
  have hcavg : circleAverage (fun z ↦ kernelLower r * logBoundary h ρ z) 0 1 =
      kernelLower r * (n * Real.log (h / 2)) := by
    have e : (fun z ↦ kernelLower r * logBoundary h ρ z) =
        fun z ↦ kernelLower r • logBoundary h ρ z := by
      funext z; simp [smul_eq_mul]
    rw [e, circleAverage_fun_smul, circleAverage_logBoundary h ρ hρ, smul_eq_mul]
  -- First term: expand and use the Poisson-log identity.
  have hmain : circleAverage (fun z ↦ poissonKernel r z * logBoundary h ρ z) 0 1 =
      n * Real.log (h / 2) + ∑ i, Real.log (quadratic r (ρ i).re) := by
    have hexpand : (fun z ↦ poissonKernel r z * logBoundary h ρ z) =
        (fun z ↦ poissonKernel r z * (n * Real.log (h / 2))) +
          ∑ i, (fun z ↦ poissonKernel r z *
            (Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)) := by
      funext z
      simp [logBoundary, mul_add, Finset.mul_sum]
    have hBi : ∀ i : Fin n, CircleIntegrable
        (fun z ↦ poissonKernel r z *
          (Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)) 0 1 := by
      intro i
      apply CircleIntegrable.continuousOn_mul _ hk'
      exact CircleIntegrable.add (circleIntegrable_log_norm_sub_const 1)
        (circleIntegrable_log_norm_sub_const 1)
    have hconst_int : CircleIntegrable
        (fun z ↦ poissonKernel r z * (n * Real.log (h / 2))) 0 1 := by
      have hsm := (circleIntegrable_const (n * Real.log (h / 2)) 0 1).continuousOn_mul hk'
      have e : (poissonKernel r * (fun _ : ℂ => n * Real.log (h / 2)))
          = (fun z ↦ poissonKernel r z * (n * Real.log (h / 2))) := by
        funext z; simp [Pi.mul_apply]
      rw [e] at hsm
      exact hsm
    rw [hexpand,
      circleAverage_add hconst_int
        (CircleIntegrable.sum Finset.univ (fun i _ => hBi i)),
      circleAverage_sum (fun i _ => hBi i)]
    have hconst : circleAverage
        (fun z ↦ poissonKernel r z * (n * Real.log (h / 2))) 0 1 =
        n * Real.log (h / 2) := by
      have e2 : (fun z ↦ poissonKernel r z * (n * Real.log (h / 2))) =
          fun z ↦ (n * Real.log (h / 2)) • poissonKernel r z := by
        funext z; simp [smul_eq_mul, mul_comm]
      rw [e2, circleAverage_fun_smul, circleAverage_poissonKernel hr0 hr1, smul_eq_mul, mul_one]
    rw [hconst]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have e3 : (fun z ↦ poissonKernel r z *
        (Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)) =
        (fun z ↦ poissonKernel r z * Real.log ‖z - ρ i‖) +
          (fun z ↦ poissonKernel r z * Real.log ‖z - conj (ρ i)‖) := by
      funext z; simp [mul_add]
    have h1' : CircleIntegrable (fun z ↦ poissonKernel r z * Real.log ‖z - ρ i‖) 0 1 := by
      have h := (circleIntegrable_log_norm_sub_const (a := ρ i) 1).continuousOn_mul hk'
      have e : (poissonKernel r * (fun x : ℂ => Real.log ‖x - ρ i‖))
          = (fun z ↦ poissonKernel r z * Real.log ‖z - ρ i‖) := by
        funext z; simp [Pi.mul_apply]
      rw [e] at h
      exact h
    have h2' : CircleIntegrable (fun z ↦ poissonKernel r z * Real.log ‖z - conj (ρ i)‖) 0 1 := by
      have h := (circleIntegrable_log_norm_sub_const (a := conj (ρ i)) 1).continuousOn_mul hk'
      have e : (poissonKernel r * (fun x : ℂ => Real.log ‖x - conj (ρ i)‖))
          = (fun z ↦ poissonKernel r z * Real.log ‖z - conj (ρ i)‖) := by
        funext z; simp [Pi.mul_apply]
      rw [e] at h
      exact h
    rw [e3, circleAverage_add h1' h2',
      circleAverage_kernel_mul_log hr0 hr1 (hρ i),
      circleAverage_kernel_mul_log hr0 hr1 (by simpa using hρ i),
      log_norm_sub_add_log_norm_sub_conj hr0 hr1 (hρ i)]
  rw [hmain, hcavg]; ring

/-- Per-radius estimate: `log(h/2)` is bounded by the weighted quadratic average. -/
lemma per_radius_estimate {n : ℕ} (hn : 0 < n) {r h : ℝ} (ρ : Fin n → ℂ)
    (hr0 : 0 < r) (hr1 : r < 1) (hh : 0 < h) (hρ : ∀ i, ‖ρ i‖ = 1)
    (hbound : ∀ z ∈ sphere (0:ℂ) 1, h^n * ∏ i, |z.re - (ρ i).re| ≤ 1) :
    Real.log (h / 2) ≤
      (∑ i, -((1 + r) / (2 * r)) * Real.log (quadratic r (ρ i).re)) / n := by
  have hr0' : 0 ≤ r := le_of_lt hr0
  have hw := continuousOn_poissonKernel hr0' hr1
  -- Step 1: the weighted average of the modified boundary function is ≤ 0.
  have hmod_int : CircleIntegrable (modifiedLogBoundary h ρ) 0 1 :=
    CircleIntegrable.congr_codiscreteWithin
      (modifiedLogBoundary_eventuallyEq h ρ).symm
      (circleIntegrable_logBoundary h ρ)
  have hw' : ContinuousOn (weight r) (sphere (0:ℂ) |1|) := by
    have hwc : ContinuousOn (weight r) (sphere (0:ℂ) 1) := by
      have e : weight r = (fun z : ℂ => poissonKernel r z) - (fun _ : ℂ => kernelLower r) := by
        funext z; simp [weight, Pi.sub_apply]
      rw [e]
      exact hw.sub continuousOn_const
    simpa using hwc
  have havg : circleAverage (fun z ↦ weight r z * modifiedLogBoundary h ρ z) 0 1 ≤ 0 := by
    apply circleAverage_mono_on_of_le_circle (hmod_int.continuousOn_mul hw')
    intro z hz
    exact mul_nonpos_of_nonneg_of_nonpos
      (weight_nonneg hr0' hr1 (by simpa using hz))
      (modifiedLogBoundary_nonpos hh ρ hρ hbound (by simpa using hz))
  -- Step 2: replace modified by original (agree off finite exceptional set).
  have hagree : circleAverage (fun z ↦ weight r z * modifiedLogBoundary h ρ z) 0 1 =
      circleAverage (fun z ↦ weight r z * logBoundary h ρ z) 0 1 := by
    apply circleAverage_congr_codiscreteWithin (hR := one_ne_zero)
    filter_upwards [modifiedLogBoundary_eventuallyEq h ρ] with z hz
    simp [hz]
  rw [hagree, circleAverage_weight_mul_logBoundary ρ hr0' hr1 hρ] at havg
  -- Step 3: rearrange. `(1 - kernelLower r) = 2*r/(1+r) > 0`.
  have hkl : 1 - kernelLower r = 2 * r / (1 + r) := by
    simp [kernelLower]; field_simp; ring
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : (0 : ℝ) < (1 + r) / (2 * r) := by positivity
  rw [hkl] at havg
  -- havg : (2*r/(1+r)) * (n * log(h/2)) + Σ log(quad) ≤ 0
  rw [le_div_iff₀ hn']
  have e : (∑ i, -((1 + r) / (2 * r)) * Real.log (quadratic r (ρ i).re))
      = -((1 + r) / (2 * r)) * ∑ i, Real.log (quadratic r (ρ i).re) := by
    rw [Finset.mul_sum]
  rw [e]
  have havg2 : (2 * r / (1 + r)) * (n * Real.log (h / 2)) ≤
      -(∑ i, Real.log (quadratic r (ρ i).re)) := by linarith
  -- Since (2r/(1+r)) = 1/c with c = (1+r)/(2r) > 0: n*L ≤ c * (-(ΣQ)).
  have hcinv : (2 * r / (1 + r)) = 1 / ((1 + r) / (2 * r)) := by
    field_simp
  have h4 : (1 / ((1 + r) / (2 * r))) * (n * Real.log (h / 2))
      = (n * Real.log (h / 2)) / ((1 + r) / (2 * r)) := by
    rw [mul_comm, ← div_eq_mul_one_div]
  rw [hcinv, h4] at havg2
  -- havg2 : (n * L) / c ≤ -(ΣQ)
  have h2 : n * Real.log (h / 2) ≤
      -((1 + r) / (2 * r)) * ∑ i, Real.log (quadratic r (ρ i).re) := by
    have h3 := (div_le_iff₀ hc).mp havg2
    linarith [h3]
  linarith [h2]

/-- Auxiliary: `log(1+w)/w → 1` as `w → 0` (punctured). -/
lemma tendsto_log_one_add_div :
    Tendsto (fun w : ℝ ↦ Real.log (1 + w) / w) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hderiv : HasDerivAt Real.log 1 1 := by
    have h := Real.hasDerivAt_log (one_ne_zero (α := ℝ))
    simpa using h
  have hslope := hderiv.tendsto_slope
  -- Unfold slope: slope Real.log 1 u = (u-1)⁻¹ * log u (since log 1 = 0).
  have hslope' : Tendsto (fun u : ℝ => (u - 1)⁻¹ * Real.log u) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
    have e : (slope Real.log 1) = (fun u : ℝ => (u - 1)⁻¹ * Real.log u) := by
      funext u
      simp [slope_def_module, Real.log_one, sub_zero, smul_eq_mul]
    rw [e] at hslope
    exact hslope
  have h1 : Tendsto (fun w : ℝ ↦ (1 + w)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 1 {1}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · -- Tendsto to nhds 1
      have h : Tendsto (fun w : ℝ ↦ (1 + w)) (nhds (0:ℝ)) (nhds 1) := by
        have hconst : Tendsto (fun _ : ℝ ↦ (1:ℝ)) (nhds (0:ℝ)) (nhds 1) := tendsto_const_nhds
        have := hconst.add tendsto_id
        simpa using this
      exact h.mono_left nhdsWithin_le_nhds
    · -- Eventually (1+w) ≠ 1
      filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
      intro hcon
      exact hw (by linarith)
  have hcomp := hslope'.comp h1
  -- hcomp : Tendsto (fun w => ((1+w) - 1)⁻¹ * Real.log (1+w)) _ (𝓝 1)
  have esimp : (fun w : ℝ ↦ ((1 + w - 1)⁻¹ * Real.log (1 + w)))
      = (fun w : ℝ ↦ Real.log (1 + w) / w) := by
    funext w
    rw [div_eq_inv_mul]
    congr 1
    congr 1
    ring
  have hcomp' : Tendsto (fun w : ℝ => (1 + w - 1)⁻¹ * Real.log (1 + w))
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have e : ((fun u : ℝ => (u - 1)⁻¹ * Real.log u) ∘ (fun w : ℝ => 1 + w))
        = (fun w : ℝ => (1 + w - 1)⁻¹ * Real.log (1 + w)) := by
      funext w; simp [Function.comp]
    rw [e] at hcomp
    exact hcomp
  rw [esimp] at hcomp'
  exact hcomp'

/-- The weight converges to the identity: `-(1+r)/(2r)·log(1-2rt+r²) → t`.
    Proved by squeezing `log(1+u)` between `u/(1+u)` and `u`. -/
lemma tendsto_weighted_log_quadratic (t : ℝ) :
    Tendsto (fun r : ℝ ↦ -((1 + r) / (2 * r)) * Real.log (quadratic r t))
      (nhdsWithin 0 (Ioi 0)) (nhds t) := by
  -- Write `quadratic r t = 1 + u(r)` with `u(r) = -2*t*r + r^2`.
  have equad : ∀ r : ℝ, quadratic r t = 1 + (-2*t*r + r^2) := fun r => by
    simp [quadratic]; ring
  -- Eventually (for small r > 0), `|u(r)| < 1/2`, so `1 + u(r) > 0`.
  have hev : ∀ᶠ r in nhdsWithin (0:ℝ) (Ioi 0), |(-2*t*r + r^2)| < 1/2 := by
    have h0 : Tendsto (fun r : ℝ ↦ -2*t*r + r^2) (nhds (0:ℝ)) (nhds 0) := by
      have e : (fun r : ℝ ↦ -2*t*r + r^2) = fun r ↦ (-2*t)*r + r^2 := by
        funext r; ring
      rw [e]
      have hlim : Tendsto (fun r : ℝ ↦ (-2*t)*r + r^2) (nhds (0:ℝ)) (nhds ((-2*t)*0 + 0^2)) := by
        have hconst : Tendsto (fun _ : ℝ ↦ -2*t) (nhds (0:ℝ)) (nhds (-2*t)) := tendsto_const_nhds
        exact (hconst.mul tendsto_id).add (tendsto_id.pow 2)
      simpa using hlim
    have hcont : Tendsto (fun r => -2*t*r + r^2) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      h0.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have := hcont.eventually (eventually_abs_sub_lt (0:ℝ) (by norm_num : (0:ℝ) < 1/2))
    simpa using this
  -- Lower and upper bounding functions, both → t.
  set L : ℝ → ℝ := fun r ↦ -((1+r)/(2*r)) * (-2*t*r + r^2) with hL
  set U : ℝ → ℝ := fun r ↦ -((1+r)/(2*r)) * ((-2*t*r + r^2) / (1 + (-2*t*r + r^2))) with hU
  have hLt : Tendsto L (nhdsWithin 0 (Ioi 0)) (nhds t) := by
    have e : L =ᶠ[nhdsWithin (0:ℝ) (Ioi 0)] fun r ↦ -((1+r) * (r - 2*t) / 2) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [Set.mem_Ioi] at hr
      simp [hL]
      field_simp
      ring
    refine Tendsto.congr' e.symm ?_
    have hlim : Tendsto (fun r : ℝ ↦ -((1+r) * (r - 2*t) / 2)) (nhds (0:ℝ)) (nhds t) := by
      have e2 : (fun r : ℝ ↦ -((1+r) * (r - 2*t) / 2)) =
          fun r ↦ (-((1+r)/2)) * (r - 2*t) := by funext r; ring
      rw [e2]
      have h1 : Tendsto (fun r : ℝ ↦ -((1+r)/2)) (nhds (0:ℝ)) (nhds (-(1/2))) := by
        have h1a : Tendsto (fun r : ℝ ↦ (1+r)/2) (nhds (0:ℝ)) (nhds (1/2)) := by
          have hconst : Tendsto (fun _ : ℝ ↦ (1:ℝ)) (nhds (0:ℝ)) (nhds 1) := tendsto_const_nhds
          have := (hconst.add tendsto_id).div_const 2
          simpa using this
        simpa using h1a.neg
      have h2 : Tendsto (fun r : ℝ ↦ (r - 2*t)) (nhds (0:ℝ)) (nhds (0 - 2*t)) := by
        have hconst : Tendsto (fun _ : ℝ ↦ 2*t) (nhds (0:ℝ)) (nhds (2*t)) := tendsto_const_nhds
        exact tendsto_id.sub hconst
      have hmul := h1.mul h2
      have e3 : (-(1/2)) * (0 - 2*t) = t := by ring
      rw [e3] at hmul
      exact hmul
    exact hlim.mono_left nhdsWithin_le_nhds
  have hUt : Tendsto U (nhdsWithin 0 (Ioi 0)) (nhds t) := by
    have e : U =ᶠ[nhdsWithin (0:ℝ) (Ioi 0)] fun r ↦ L r / (1 + (-2*t*r + r^2)) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [Set.mem_Ioi] at hr
      simp [hU, hL]
      field_simp
    refine Tendsto.congr' e.symm ?_
    have hden : Tendsto (fun r : ℝ ↦ (1 + (-2*t*r + r^2))) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
      have h0 : Tendsto (fun r : ℝ ↦ (1 + (-2*t*r + r^2))) (nhds (0:ℝ)) (nhds (1 + (-2*t*0 + 0^2))) := by
        have h1const : Tendsto (fun _ : ℝ ↦ (1:ℝ)) (nhds (0:ℝ)) (nhds 1) := tendsto_const_nhds
        have h2const : Tendsto (fun _ : ℝ ↦ -2*t) (nhds (0:ℝ)) (nhds (-2*t)) := tendsto_const_nhds
        have hmul : Tendsto (fun r : ℝ ↦ (-2*t)*r) (nhds (0:ℝ)) (nhds ((-2*t)*0)) :=
          h2const.mul tendsto_id
        have hadd : Tendsto (fun r : ℝ ↦ (-2*t)*r + r^2) (nhds (0:ℝ)) (nhds ((-2*t)*0 + 0^2)) :=
          hmul.add (tendsto_id.pow 2)
        exact h1const.add hadd
      have h0s : Tendsto (fun r : ℝ ↦ (1 + (-2*t*r + r^2))) (nhds (0:ℝ)) (nhds 1) := by
        simpa using h0
      exact h0s.mono_left nhdsWithin_le_nhds
    have hdiv := hLt.div hden (by norm_num : (1:ℝ) ≠ 0)
    have e : (L / fun r => 1 + (-2*t*r + r^2))
        = (fun r => L r / (1 + (-2*t*r + r^2))) := by
      funext r; simp [Pi.div_apply]
    rw [e, div_one] at hdiv
    exact hdiv
  -- Squeeze: L(r) ≤ target ≤ U(r) eventually.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLt hUt ?_ ?_
  · filter_upwards [hev, self_mem_nhdsWithin] with r hr hrr
    simp only [Set.mem_Ioi] at hrr
    have h1u : (0:ℝ) < 1 + (-2*t*r + r^2) := by
      have hab := abs_lt.mp hr
      linarith [hab.1]
    have hlog_le : Real.log (1 + (-2*t*r + r^2)) ≤ -2*t*r + r^2 := by
      have hle := Real.log_le_sub_one_of_pos h1u
      linarith
    have htarget_eq : -((1 + r) / (2 * r)) * Real.log (quadratic r t)
        = -((1+r)/(2*r)) * Real.log (1 + (-2*t*r + r^2)) := by rw [equad]
    rw [htarget_eq]
    have hnonpos : -((1+r)/(2*r)) ≤ (0:ℝ) := by
      have h1 : (0:ℝ) < 1 + r := by linarith
      have h2 : (0:ℝ) < 2 * r := by linarith
      have h3 : (0:ℝ) < (1+r)/(2*r) := div_pos h1 h2
      linarith
    have hmul := mul_le_mul_of_nonpos_left hlog_le hnonpos
    simpa [hL] using hmul
  · filter_upwards [hev, self_mem_nhdsWithin] with r hr hrr
    simp only [Set.mem_Ioi] at hrr
    have h1u : (0:ℝ) < 1 + (-2*t*r + r^2) := by
      have hab := abs_lt.mp hr
      linarith [hab.1]
    have hlog_ge : (-2*t*r + r^2) / (1 + (-2*t*r + r^2)) ≤
        Real.log (1 + (-2*t*r + r^2)) := by
      have hpos : (0:ℝ) < 1 / (1 + (-2*t*r + r^2)) := by positivity
      have h2 := Real.log_le_sub_one_of_pos hpos
      rw [Real.log_div (by norm_num) (ne_of_gt h1u), Real.log_one] at h2
      -- h2 : -Real.log (1+u) ≤ 1/(1+u) - 1 = -u/(1+u)
      have h3 : (1:ℝ) / (1 + (-2*t*r + r^2)) - 1 = -((-2*t*r + r^2) / (1 + (-2*t*r + r^2))) := by
        have hne : (1:ℝ) + (-2*t*r + r^2) ≠ 0 := ne_of_gt h1u
        have e1 : (1:ℝ) / (1 + (-2*t*r + r^2)) - 1
            = (1 - (1 + (-2*t*r + r^2))) / (1 + (-2*t*r + r^2)) := by
          rw [sub_div, div_self hne]
        rw [e1]
        have e2 : (1 - (1 + (-2*t*r + r^2))) / (1 + (-2*t*r + r^2))
            = -(-2*t*r + r^2) / (1 + (-2*t*r + r^2)) := by ring
        rw [e2, neg_div]
      rw [h3] at h2
      linarith
    have htarget_eq : -((1 + r) / (2 * r)) * Real.log (quadratic r t)
        = -((1+r)/(2*r)) * Real.log (1 + (-2*t*r + r^2)) := by rw [equad]
    rw [htarget_eq]
    have hnonpos : -((1+r)/(2*r)) ≤ (0:ℝ) := by
      have h1 : (0:ℝ) < 1 + r := by linarith
      have h2 : (0:ℝ) < 2 * r := by linarith
      have h3 : (0:ℝ) < (1+r)/(2*r) := div_pos h1 h2
      linarith
    have hmul := mul_le_mul_of_nonpos_left hlog_ge hnonpos
    simpa [hU] using hmul

/-- Every `t ∈ [-1,1]` lifts to a point on the unit circle with real part `t`. -/
lemma exists_circle_lift {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    ∃ ρ : ℂ, ρ.re = t ∧ ‖ρ‖ = 1 := by
  obtain ⟨h1, h2⟩ := ht
  have hnn : (0:ℝ) ≤ 1 - t^2 := by nlinarith
  refine ⟨⟨t, Real.sqrt (1 - t^2)⟩, rfl, ?_⟩
  have hsq : ‖(⟨t, Real.sqrt (1 - t^2)⟩ : ℂ)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Real.mul_self_sqrt hnn]
    ring
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · have := norm_nonneg (⟨t, Real.sqrt (1 - t^2)⟩ : ℂ)
    linarith

/-- **The 1D weighted-Jensen lemma.** Points in `[-1,1]` whose product of
    distances to every `y ∈ [-1,1]` is small must have mean at least `log(h/2)`. -/
theorem weighted_jensen {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h)
    (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc (-1) 1)
    (hbound : ∀ y ∈ Set.Icc (-1) 1, h^n * ∏ i, |y - t i| ≤ 1) :
    Real.log (h/2) ≤ (∑ i, t i) / n := by
  -- Lift each `t i` to the unit circle.
  choose ρ hρ using fun i => exists_circle_lift (ht i)
  have hρre : ∀ i, (ρ i).re = t i := fun i => (hρ i).1
  have hρn : ∀ i, ‖ρ i‖ = 1 := fun i => (hρ i).2
  -- Transfer the product bound to the circle.
  have hbound' : ∀ z ∈ sphere (0:ℂ) 1, h^n * ∏ i, |z.re - (ρ i).re| ≤ 1 := by
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa [mem_sphere_iff_norm] using hz
    have hre : z.re ∈ Set.Icc (-1) 1 := by
      have hab := abs_re_le_norm z
      rw [hzn] at hab
      simp only [Set.mem_Icc]
      have := abs_le.mp hab
      constructor <;> linarith
    have hb := hbound z.re hre
    simpa [hρre] using hb
  -- The per-radius estimate: `log(h/2) ≤ G(r)` for `r ∈ (0,1)`.
  have hG : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      Real.log (h/2) ≤
        (∑ i, -((1 + r) / (2 * r)) * Real.log (quadratic r (ρ i).re)) / n := by
    intro r hr
    have hmem : r ∈ Set.Ioo (0:ℝ) 1 := hr
    simp only [Set.mem_Ioo] at hmem
    exact per_radius_estimate hn ρ hmem.1 hmem.2 hh hρn hbound'
  -- `G(r) → t̄` as `r → 0⁺`.
  have hlim : Tendsto
      (fun r ↦ (∑ i, -((1 + r) / (2 * r)) * Real.log (quadratic r (ρ i).re)) / n)
      (nhdsWithin 0 (Ioi 0)) (nhds ((∑ i, t i) / n)) := by
    have hsum : Tendsto
        (fun r ↦ ∑ i, -((1 + r) / (2 * r)) * Real.log (quadratic r (ρ i).re))
        (nhdsWithin 0 (Ioi 0)) (nhds (∑ i, t i)) := by
      apply tendsto_finset_sum
      intro i _
      have hti := tendsto_weighted_log_quadratic (t i)
      simpa [← hρre i] using hti
    exact hsum.div_const n
  -- Conclude by taking the limit.
  apply ge_of_tendsto hlim
  have hmem : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Ioi 0) := by
    have e : Set.Ioo (0:ℝ) 1 = Set.Ioi 0 ∩ Set.Iio 1 := by
      ext x
      simp only [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio, Set.mem_inter_iff]
    rw [e]
    exact inter_mem_nhdsWithin (Set.Ioi 0) (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hmem] with r hr
  exact hG r hr

end JensenWeight
end JSP000868
