/-
Main theorem for JSP-000868 (Pommerenke 1959).

If `f : ℂ[X]` is monic and the sublevel set `E = {z | ‖f.eval z‖ < 1}` is
connected, then `E` is contained in some open disk of radius 2.

Proof strategy. Let `n = f.natDegree`, `α_1, …, α_n` the complex roots
(counting multiplicity), and `c = (∑ α_i)/n` the centroid.
If `n = 0` then `f = 1` and `E = ∅`. Assume `n ≥ 1`.

For `z ∈ E` we show `‖z - c‖ < 2`. It suffices to show `‖z - c‖ ≤ 2`:
since `E` is open, a ray argument upgrades `≤` to `<`.

If `z = c` this is trivial. Otherwise put `d = ‖z - c‖ > 0`,
`u = (z - c)/d` (a unit vector), and let `π(w) = Re((w - c) * conj u)`
be the real projection along `u`. The projected roots `x_i = π(α_i)`
satisfy `∑ x_i = 0` (because `∑ (α_i - c) = 0`).

The set `π '' E` is preconnected (continuous image of the connected set `E`)
and contains both `d = π(z)` and the `x_i = π(α_i)` (the roots lie in `E`
since `f(α_i) = 0`). Let `A ≤ B` be the min/max of `{d} ∪ {x_i}`; then
`[A, B] ⊆ π '' E`.

For `y ∈ [A, B]`, choose `w ∈ E` with `π(w) = y`. Since `π` is 1-Lipschitz,
`∏ |y - x_i| ≤ ∏ ‖w - α_i‖ = ‖f(w)‖ < 1`.
The one-dimensional corollary `oneDim_bound` then gives `B - 0 ≤ 2`,
and `d ≤ B` yields `d ≤ 2`.
-/
import JSP000868.JensenWeight
import Mathlib.Analysis.Complex.Polynomial.Basic

open Complex Filter Metric Set Topology
open scoped Polynomial Topology ComplexConjugate

noncomputable section

namespace JSP000868

/-- For `s > 0`, `s * (1 - log s) ≤ 1` (maximum of `s ↦ s(1 - log s)` at `s = 1`). -/
lemma phi_le_one {s : ℝ} (hs : 0 < s) : s * (1 - Real.log s) ≤ 1 := by
  have h1 : 1 - 1 / s ≤ Real.log s := by
    have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / s by positivity)
    rw [Real.log_div (by norm_num) (ne_of_gt hs), Real.log_one, zero_sub] at h2
    linarith
  have h3 : 1 - Real.log s ≤ 1 / s := by linarith
  calc s * (1 - Real.log s)
      ≤ s * (1 / s) := mul_le_mul_of_nonneg_left h3 (le_of_lt hs)
    _ = 1 := by field_simp

/-- One-dimensional corollary: points in `[A,B]` whose product of distances
    to every `y ∈ [A,B]` is at most 1 satisfy `B - mean ≤ 2`.
    Proved by the affine change `t_i = (x_i - m)/h` reducing to `weighted_jensen`. -/
theorem oneDim_bound {n : ℕ} (hn : 0 < n) {A B : ℝ} (hAB : A ≤ B)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc A B)
    (hbound : ∀ y ∈ Icc A B, ∏ i, |y - x i| ≤ 1) :
    B - (∑ i, x i) / n ≤ 2 := by
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnpos : (n:ℝ) ≠ 0 := ne_of_gt hn'
  set m := (A + B) / 2 with hm_def
  set h := (B - A) / 2 with hh_def
  have hmA : m - h = A := by rw [hm_def, hh_def]; ring
  have hmB : m + h = B := by rw [hm_def, hh_def]; ring
  have hh_nonneg : 0 ≤ h := by rw [hh_def]; linarith
  rcases eq_or_lt_of_le hh_nonneg with hh0 | hhpos
  · -- Degenerate case `A = B`: everything equals `B`.
    have hAeqB : A = B := by linarith
    have hxB : ∀ i, x i = B := fun i => by
      have hmem := hx i
      rw [hAeqB, Set.mem_Icc] at hmem
      exact le_antisymm hmem.2 hmem.1
    have hsum : ∑ i, x i = n * B := by
      trans ∑ _i : Fin n, B
      · apply Finset.sum_congr rfl; intro i _; exact hxB i
      · simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    rw [hsum]
    have hdiv : (n:ℝ) * B / n = B := by field_simp
    rw [hdiv, sub_self]
    norm_num
  · -- Main case `h > 0`: normalize to `[-1,1]` and apply `weighted_jensen`.
    have ht_mem : ∀ i, (x i - m) / h ∈ Icc (-1:ℝ) 1 := by
      intro i
      have hmem := hx i
      rw [Set.mem_Icc] at hmem ⊢
      have h1 : -h ≤ x i - m := by linarith [hmem.1, hmA]
      have h2 : x i - m ≤ h := by linarith [hmem.2, hmB]
      constructor
      · rw [le_div_iff₀ hhpos]; linarith
      · rw [div_le_iff₀ hhpos]; linarith
    have hbound' : ∀ s ∈ Icc (-1:ℝ) 1, h ^ n * ∏ i, |s - (x i - m) / h| ≤ 1 := by
      intro s hs
      have hyAB : m + h * s ∈ Icc A B := by
        rw [Set.mem_Icc] at hs ⊢
        constructor
        · rw [← hmA]; nlinarith [hs.1, hhpos, le_of_lt hhpos]
        · rw [← hmB]; nlinarith [hs.2, hhpos, le_of_lt hhpos]
      have hb := hbound (m + h * s) hyAB
      have e : ∏ i, |s - (x i - m) / h| = (∏ i, |m + h * s - x i|) / h ^ n := by
        have hi : ∀ i, |s - (x i - m) / h| = |m + h * s - x i| / h := by
          intro i
          have e1 : s - (x i - m) / h = (m + h * s - x i) / h := by
            field_simp; ring
          rw [e1, abs_div, abs_of_pos hhpos]
        rw [Finset.prod_congr rfl (fun i _ => hi i), Finset.prod_div_distrib]
        congr 1
        simp [Finset.prod_const, Finset.card_univ]
      have hne : (h ^ n : ℝ) ≠ 0 := ne_of_gt (pow_pos hhpos n)
      have hcancel : h ^ n * ((∏ i, |m + h * s - x i|) / h ^ n)
          = ∏ i, |m + h * s - x i| := by
        field_simp
      rw [e, hcancel]
      exact hb
    have hjensen := JensenWeight.weighted_jensen hn hhpos (fun i => (x i - m) / h)
      ht_mem hbound'
    -- Simplify the mean: `(∑ (x_i - m)/h)/n = ((∑ x_i)/n - m)/h`.
    have hmean : (∑ i, (x i - m) / h) / n = ((∑ i, x i) / n - m) / h := by
      have hne : (h : ℝ) ≠ 0 := ne_of_gt hhpos
      rw [div_eq_div_iff hnpos hne]
      have lhs : (∑ i, (x i - m) / h) * h = (∑ i, x i) - ↑n * m := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_assoc, inv_mul_cancel₀ hne,
          mul_one, Finset.sum_sub_distrib]
        congr 1
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have rhs : ((∑ i, x i) / ↑n - m) * ↑n = (∑ i, x i) - ↑n * m := by
        rw [sub_mul, div_mul_cancel₀ _ hnpos, mul_comm]
      rw [lhs, rhs]
    rw [hmean] at hjensen
    -- Hence `m + h*log(h/2) ≤ mean(x)`.
    have hxbar : m + h * Real.log (h / 2) ≤ (∑ i, x i) / n := by
      have h2 := (le_div_iff₀ hhpos).mp hjensen
      linarith
    have hphi : h * (1 - Real.log (h / 2)) ≤ 2 := by
      have h1 := phi_le_one (show (0:ℝ) < h / 2 by positivity)
      have e2 : h * (1 - Real.log (h / 2)) = 2 * ((h / 2) * (1 - Real.log (h / 2))) := by
        ring
      rw [e2]
      linarith
    rw [← hmB]
    linarith

/-- Any multiset is the `Finset.univ`-image of a `Fin`-indexed family. -/
lemma Multiset.exists_eq_map_fin_univ {α : Type*} (s : Multiset α) :
    ∃ f : Fin s.card → α, Multiset.map f Finset.univ.val = s := by
  have hlen : s.toList.length = s.card := Multiset.length_toList s
  set f : Fin s.card → α := fun i => s.toList[i.val]'(by rw [hlen]; exact i.isLt) with hf_def
  have hof : List.ofFn f = s.toList := by
    rw [hf_def]
    refine List.ext_getElem (by rw [List.length_ofFn, ← hlen]) fun k h1 h2 => ?_
    rw [List.getElem_ofFn]
  refine ⟨f, ?_⟩
  rw [Fin.univ_val_map, hof, Multiset.coe_toList]

/-- A monic complex polynomial of positive degree has a `Fin n`-indexed
    family of roots with `f.eval w = ∏ i, (w - α i)` and `f.eval (α i) = 0`. -/
lemma exists_root_family {f : ℂ[X]} (hf : f.Monic) {n : ℕ} (hn : f.natDegree = n)
    (hnsplit : f.Splits) (hnpos : 0 < n) :
    ∃ α : Fin n → ℂ, (∀ w, f.eval w = ∏ i, (w - α i)) ∧ ∀ i, f.eval (α i) = 0 := by
  have hcard : f.roots.card = n :=
    (Polynomial.splits_iff_card_roots.mp hnsplit).trans hn
  obtain ⟨α₀, hα₀⟩ := Multiset.exists_eq_map_fin_univ f.roots
  -- Index bound for transporting `Fin f.roots.card` to `Fin n`.
  have hlt : ∀ i : Fin n, i.val < f.roots.card := fun i => by
    rw [hcard]; exact i.isLt
  -- Define the `Fin n`-indexed family directly (avoids `▸` motive issues).
  set α : Fin n → ℂ := fun i => α₀ ⟨i.val, hlt i⟩ with hα_def
  have hmem : ∀ i : Fin n, α i ∈ f.roots := by
    intro i
    have hj : (⟨i.val, hlt i⟩ : Fin f.roots.card) ∈ Finset.univ.val := by simp
    have h2 : α₀ ⟨i.val, hlt i⟩ ∈ Multiset.map α₀ Finset.univ.val :=
      Multiset.mem_map.mpr ⟨_, hj, rfl⟩
    rw [hα₀] at h2
    simpa [hα_def] using h2
  have hroot : ∀ i : Fin n, f.eval (α i) = 0 :=
    fun i => Polynomial.isRoot_of_mem_roots (hmem i)
  refine ⟨α, ?_, hroot⟩
  intro w
  have hroots_eq := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf
    (Polynomial.splits_iff_card_roots.mp hnsplit)
  have heval : f.eval w = (Multiset.map (fun a => w - a) f.roots).prod := by
    have hfactor : f.eval w
        = ((f.roots.map fun a => Polynomial.X - Polynomial.C a).prod).eval w := by
      rw [hroots_eq]
    rw [hfactor, Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [heval, ← hα₀, Multiset.map_map, Fin.univ_val_map, Multiset.prod_coe, List.prod_ofFn]
  -- Goal: `∏ i : Fin f.roots.card, ((fun a => w - a) ∘ α₀) i = ∏ i : Fin n, (w - α i)`.
  refine Fintype.prod_equiv (finCongr hcard) _ _ fun i => ?_
  simp only [hα_def, Function.comp_apply]
  -- `(finCongr hcard i).val = i.val` by definition; conclude by proof irrelevance.
  rfl

/-- The sublevel set `E` is open. -/
lemma isOpen_sublevel (f : ℂ[X]) : IsOpen {z : ℂ | ‖f.eval z‖ < 1} := by
  have hcont : Continuous (fun z : ℂ => ‖f.eval z‖) :=
    continuous_norm.comp (Polynomial.continuous f)
  exact hcont.isOpen_preimage _ isOpen_Iio

/-- Pommerenke (1959): a monic polynomial whose open unit-modulus sublevel set
    is connected has that sublevel set contained in an open disk of radius 2. -/
theorem jsp000868 (f : ℂ[X]) (hf : f.Monic)
    (hE : IsConnected {z : ℂ | ‖f.eval z‖ < 1}) :
    ∃ c : ℂ, {z : ℂ | ‖f.eval z‖ < 1} ⊆ Metric.ball c 2 := by
  have hEopen := isOpen_sublevel f
  have hnsplit : f.Splits := IsAlgClosed.splits f
  set E := {z : ℂ | ‖f.eval z‖ < 1} with hE_def
  -- Degree zero case: `f = 1`, `E = ∅`.
  rcases Nat.eq_zero_or_pos f.natDegree with hn0 | hnPos
  · have hf1 : f = 1 := by
      apply Polynomial.ext
      intro m
      by_cases hm : m = 0
      · subst hm
        have hlead : f.leadingCoeff = 1 := hf.leadingCoeff
        rw [Polynomial.leadingCoeff, hn0] at hlead
        simpa using hlead
      · have h0 : f.coeff m = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hn0]; exact Nat.pos_of_ne_zero hm)
        rw [h0, Polynomial.coeff_one, if_neg hm]
    refine ⟨0, ?_⟩
    rw [hE_def, hf1]
    intro z hz
    simp at hz
  · -- Positive degree: use the root family and the projection argument.
    obtain ⟨α, heval, hroot⟩ :=
      exists_root_family hf rfl hnsplit hnPos
    -- Centroid of the roots.
    have hn' : (0:ℝ) < f.natDegree := Nat.cast_pos.mpr hnPos
    set c := (∑ i, α i) / f.natDegree with hc_def
    refine ⟨c, ?_⟩
    -- It suffices to show `‖z - c‖ ≤ 2` for `z ∈ E` (openness upgrades to `<`).
    have hle : ∀ z ∈ {z : ℂ | ‖f.eval z‖ < 1}, ‖z - c‖ ≤ 2 := by
      intro z hz
      rw [Set.mem_setOf_eq] at hz
      by_cases hzc : z = c
      · rw [hzc, sub_self, norm_zero]; norm_num
      · -- Set up the projection.
        have hdpos : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
        set d : ℝ := ‖z - c‖ with hd_def
        set u : ℂ := (z - c) / (d : ℂ) with hu_def
        have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hdpos
        have hu1 : ‖u‖ = 1 := by
          have hnorm : ‖(d : ℂ)‖ = d := by
            simp [abs_of_pos hdpos]
          rw [hu_def, norm_div, ← hd_def, hnorm, div_self (ne_of_gt hdpos)]
        -- The real projection `π(w) = Re((w - c) * conj u)`.
        set π : ℂ → ℝ := fun w => ((w - c) * conj u).re with hπ_def
        have hπcont : Continuous π := by
          rw [hπ_def]
          apply Complex.continuous_re.comp
          apply Continuous.mul
          · exact continuous_id.sub continuous_const
          · exact continuous_const
        -- Projected roots; their sum is zero.
        set x : Fin f.natDegree → ℝ := fun i => π (α i) with hx_def
        have hsum0 : ∑ i, x i = 0 := by
          have e1 : ∑ i, x i = ((∑ i, (α i - c)) * conj u).re := by
            simp only [hx_def, hπ_def]
            rw [← Complex.re_sum, ← Finset.sum_mul]
          have e2 : ∑ i, (α i - c) = 0 := by
            have e3 : ∑ i, (α i - c) = (∑ i, α i) - f.natDegree * c := by
              simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                nsmul_eq_mul]
            have hnC : ((f.natDegree:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hnPos)
            rw [e3, hc_def, mul_div_cancel₀ _ hnC, sub_self]
          rw [e1, e2, zero_mul, Complex.zero_re]
        -- `π '' E` is preconnected and contains `d` and the `x_i`.
        have hpre := hE.isPreconnected.image π hπcont.continuousOn
        have hπz : π z = d := by
          have e1 : (z - c) = (d : ℂ) * u := by
            rw [hu_def, mul_div_cancel₀ _ hdne]
          have hns : Complex.normSq u = 1 := by
            rw [Complex.normSq_eq_norm_sq, hu1, one_pow]
          simp only [hπ_def, e1, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
            Complex.ofReal_re, hns, mul_one]
        have hdmem : d ∈ π '' E := ⟨z, hz, hπz⟩
        have hxmem : ∀ i, x i ∈ π '' E := by
          intro i
          have hαE : α i ∈ {z : ℂ | ‖f.eval z‖ < 1} := by
            rw [Set.mem_setOf_eq, hroot i, norm_zero]
            norm_num
          exact ⟨α i, hαE, rfl⟩
        -- The finite set of projected points; `A = min`, `B = max`.
        set S : Finset ℝ := Finset.univ.image x ∪ {d} with hS_def
        have hSne : S.Nonempty := by
          rw [hS_def, Finset.union_nonempty]
          exact Or.inr (Finset.singleton_nonempty d)
        set A := S.min' hSne with hA_def
        set B := S.max' hSne with hB_def
        have hAB : A ≤ B := Finset.min'_le_max' _ _
        have hAmem : A ∈ π '' E := by
          have hmem : A ∈ Finset.univ.image x ∪ {d} := Finset.min'_mem S hSne
          rcases Finset.mem_union.mp hmem with h | h
          · obtain ⟨i, _, hxi⟩ := Finset.mem_image.mp h
            have hxe := hxmem i
            rwa [hxi] at hxe
          · rw [Finset.mem_singleton.mp h]; exact hdmem
        have hBmem : B ∈ π '' E := by
          have hmem : B ∈ Finset.univ.image x ∪ {d} := Finset.max'_mem S hSne
          rcases Finset.mem_union.mp hmem with h | h
          · obtain ⟨i, _, hxi⟩ := Finset.mem_image.mp h
            have hxe := hxmem i
            rwa [hxi] at hxe
          · rw [Finset.mem_singleton.mp h]; exact hdmem
        have hxAB : ∀ i, x i ∈ Icc A B := by
          intro i
          have hmem : x i ∈ S := by
            rw [hS_def]
            apply Finset.mem_union.mpr
            exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
          rw [Set.mem_Icc]
          exact ⟨Finset.min'_le _ _ hmem, Finset.le_max' _ _ hmem⟩
        have hdAB : d ∈ Icc A B := by
          have hmem : d ∈ S := by
            rw [hS_def]
            apply Finset.mem_union.mpr
            exact Or.inr (Finset.mem_singleton_self d)
          rw [Set.mem_Icc]
          exact ⟨Finset.min'_le _ _ hmem, Finset.le_max' _ _ hmem⟩
        -- The product bound on `[A,B]`.
        have hbound : ∀ y ∈ Icc A B, ∏ i, |y - x i| ≤ 1 := by
          intro y hy
          -- `y ∈ π '' E` by preconnectedness (`OrdConnected`).
          have hyE : y ∈ π '' E := by
            have hord : OrdConnected (π '' E) := isPreconnected_iff_ordConnected.mp hpre
            have hIcc : Icc A B ⊆ π '' E := hord.out hAmem hBmem
            exact hIcc hy
          obtain ⟨w, hwE, hπw⟩ := hyE
          rw [hE_def, Set.mem_setOf_eq] at hwE
          -- `∏|y - x_i| ≤ ∏‖w - α_i‖ = ‖f.eval w‖ < 1`.
          have hle_prod : ∏ i, |y - x i| ≤ ∏ i, ‖w - α i‖ := by
            apply Finset.prod_le_prod
            · intro i _; exact abs_nonneg _
            · intro i _
              -- `|y - x_i| = |π(w) - π(α_i)| ≤ ‖w - α_i‖`.
              have e : y - x i = ((w - α i) * conj u).re := by
                rw [hx_def, ← hπw]
                simp only [hπ_def]
                rw [← Complex.sub_re]
                congr 1
                rw [← sub_mul]
                congr 1
                ring
              rw [e]
              calc |(((w - α i) * conj u).re)| ≤ ‖(w - α i) * conj u‖ :=
                    Complex.abs_re_le_norm _
                _ = ‖w - α i‖ * ‖conj u‖ := norm_mul _ _
                _ = ‖w - α i‖ := by rw [Complex.norm_conj, hu1, mul_one]
          have heq : ∏ i, ‖w - α i‖ = ‖f.eval w‖ := by
            rw [heval w, norm_prod]
          rw [heq] at hle_prod
          exact le_of_lt (lt_of_le_of_lt hle_prod hwE)
        -- Apply the 1D bound.
        have h1d := oneDim_bound hnPos hAB x hxAB hbound
        rw [hsum0] at h1d
        -- `h1d : B - 0/n ≤ 2`, i.e. `B ≤ 2`.
        simp at h1d
        have hdB : d ≤ B := (Set.mem_Icc.mp hdAB).2
        linarith
    -- Upgrade `≤ 2` to `< 2` via openness (ray argument).
    intro z hz
    have h2 := hle z hz
    by_cases hzc : z = c
    · rw [hzc]
      simp [Metric.ball]
    · -- Points on the ray beyond `z` are still in `E`.
      have hγ : ∀ᶠ t in 𝓝 (1:ℝ), (c + t • (z - c)) ∈ {z : ℂ | ‖f.eval z‖ < 1} := by
        have hcont : Continuous (fun t : ℝ => c + t • (z - c)) := by
          apply Continuous.add continuous_const
          apply Continuous.smul continuous_id continuous_const
        have hlim : Tendsto (fun t : ℝ => c + t • (z - c)) (𝓝 1) (𝓝 z) := by
          have h1 : Tendsto (fun t : ℝ => c + t • (z - c)) (𝓝 (1:ℝ)) (𝓝 (c + (1:ℝ) • (z - c))) :=
            hcont.tendsto (1:ℝ)
          simpa using h1
        exact hlim.eventually (hEopen.mem_nhds hz)
      have hγ' : {t : ℝ | (c + t • (z - c)) ∈ {z : ℂ | ‖f.eval z‖ < 1}} ∈ 𝓝 (1:ℝ) := hγ
      rw [Metric.mem_nhds_iff] at hγ'
      obtain ⟨ε, hεpos, hε⟩ := hγ'
      set t := 1 + ε / 2 with ht_def
      have ht1 : 1 < t := by rw [ht_def]; linarith
      have htpos : (0:ℝ) < t := by linarith
      have htz : t ∈ Metric.ball (1:ℝ) ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have e : t - 1 = ε / 2 := by rw [ht_def]; ring
        rw [e, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
        linarith
      have hmem : (c + t • (z - c)) ∈ {z : ℂ | ‖f.eval z‖ < 1} := hε htz
      have h3 := hle _ hmem
      -- `‖(c + t•(z-c)) - c‖ = t * ‖z - c‖ ≤ 2`, so `‖z-c‖ ≤ 2/t < 2`.
      have hnorm : ‖(c + t • (z - c)) - c‖ = t * ‖z - c‖ := by
        have e : (c + t • (z - c)) - c = t • (z - c) := by abel
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      rw [hnorm] at h3
      have hle_div : ‖z - c‖ ≤ 2 / t := by
        have h3' : ‖z - c‖ * t ≤ 2 := by linarith [h3]
        exact (le_div_iff₀ htpos).mpr h3'
      have h4 : (2:ℝ) / t < 2 := by
        rw [div_lt_iff₀ htpos]
        nlinarith [ht1]
      have htz2 : ‖z - c‖ < 2 := lt_of_le_of_lt hle_div h4
      rw [Metric.mem_ball, dist_eq_norm]
      exact htz2

end JSP000868
