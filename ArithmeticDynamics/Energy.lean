/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XV: the Kuramoto energy, its gradient structure, regularity of the vector field,
the Fréchet derivative at twisted states, and the quarter-twist energy formula (Theorem 5.6).
-/
import Mathlib
import ArithmeticDynamics.MeanValue

namespace ArithmeticDynamics

open Finset Real

variable {n : ℕ} [NeZero n]

/-- The Kuramoto energy `E(θ) = -(K/(2φ(n))) ∑_i ∑_u cos(θ_{i+u} - θ_i)` on `X_n`. -/
noncomputable def energy (n : ℕ) [NeZero n] (K : ℝ) (θ : ZMod n → ℝ) : ℝ :=
  -(K / (2 * (Nat.totient n : ℝ))) * ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, cos (θ (i + u) - θ i)

/-- Reindexing identity behind the gradient structure. -/
theorem sum_sin_shift (x v : ZMod n → ℝ) :
    ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) * v (i + u)
      = -∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) * v i := by
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  have h1 : ∀ u : (ZMod n)ˣ, ∑ i : ZMod n, sin (x (i + u) - x i) * v (i + u)
      = -∑ j : ZMod n, sin (x (j + ((-u : (ZMod n)ˣ) : ZMod n)) - x j) * v j := by
    intro u
    rw [← Equiv.sum_comp (Equiv.subRight (u : ZMod n))]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Equiv.subRight_apply, sub_add_cancel, Units.val_neg]
    rw [← sub_eq_add_neg, ← neg_sub (x (j - u)) (x j), sin_neg]
    ring
  rw [sum_congr rfl fun u _ => h1 u, sum_neg_distrib, neg_inj]
  exact Fintype.sum_equiv (Equiv.neg (ZMod n)ˣ)
    (fun u => ∑ j : ZMod n, sin (x (j + ((-u : (ZMod n)ˣ) : ZMod n)) - x j) * v j)
    (fun u => ∑ j : ZMod n, sin (x (j + (u : ZMod n)) - x j) * v j) (fun u => rfl)

/-- The Kuramoto vector field has zero sum, so `∑ θ_i` is conserved. -/
theorem sum_kuramotoField (K : ℝ) (x : ZMod n → ℝ) : ∑ i, kuramotoField n K x i = 0 := by
  unfold kuramotoField
  rw [← mul_sum]
  have h := sum_sin_shift x (fun _ => 1)
  simp only [mul_one] at h
  have : ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) = 0 := by linarith
  rw [this, mul_zero]

/-- **Gradient structure.**  The Kuramoto field is `-∇E`: along every line,
`d/dt E(x + t v)|_{t=0} = -∑_i F(x)_i v_i`. -/
theorem energy_hasDerivAt_line (K : ℝ) (x v : ZMod n → ℝ) :
    HasDerivAt (fun t : ℝ => energy n K (x + t • v)) (-∑ i, kuramotoField n K x i * v i) 0 := by
  unfold energy
  have hterm : ∀ (i : ZMod n) (u : (ZMod n)ˣ),
      HasDerivAt (fun t : ℝ => cos ((x + t • v) (i + u) - (x + t • v) i))
        (-sin (x (i + u) - x i) * (v (i + u) - v i)) 0 := by
    intro i u
    have hl : HasDerivAt (fun t : ℝ => (x + t • v) (i + u) - (x + t • v) i)
        (v (i + u) - v i) 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ha := ((hasDerivAt_id (0 : ℝ)).mul_const (v (i + u))).const_add (x (i + u))
      have hb := ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i)
      have := ha.fun_sub hb
      simpa using this
    have := hl.cos
    simpa [mul_comm] using this
  have hsum := HasDerivAt.fun_sum (u := univ) fun i _ =>
    HasDerivAt.fun_sum (u := univ) fun u _ => hterm i u
  convert hsum.const_mul (-(K / (2 * (Nat.totient n : ℝ)))) using 1
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  have hs := sum_sin_shift x v
  have e1 : ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, -sin (x (i + u) - x i) * (v (i + u) - v i)
      = -(∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) * v (i + u))
        + ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) * v i := by
    rw [← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    ring
  rw [e1, hs]
  unfold kuramotoField
  simp_rw [mul_assoc, ← mul_sum, sum_mul]
  field_simp
  ring

/-! ### Regularity of the vector field -/

theorem contDiff_kuramotoField (K : ℝ) : ContDiff ℝ 1 (kuramotoField n K) := by
  unfold kuramotoField
  fun_prop

theorem lipschitz_kuramotoField (K : ℝ) : ∃ L, LipschitzWith L (kuramotoField n K) := by
  refine ⟨⟨2 * |K|, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hd : 0 ≤ dist x y := dist_nonneg
  show dist (kuramotoField n K x) (kuramotoField n K y) ≤ 2 * |K| * dist x y
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [Real.dist_eq]
  unfold kuramotoField
  rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_div, abs_of_pos hφ]
  have hb : ∀ u : (ZMod n)ˣ, |sin (x (i + u) - x i) - sin (y (i + u) - y i)| ≤ 2 * dist x y := by
    intro u
    refine (abs_sin_sub_sin_le _ _).trans ?_
    have h1 : |x (i + u) - y (i + u)| ≤ dist x y := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist x y _
    have h2 : |x i - y i| ≤ dist x y := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist x y _
    calc |x (i + u) - x i - (y (i + u) - y i)| = |(x (i + u) - y (i + u)) - (x i - y i)| := by
          ring_nf
      _ ≤ |x (i + u) - y (i + u)| + |x i - y i| := abs_sub _ _
      _ ≤ 2 * dist x y := by linarith
  calc |K| / (Nat.totient n : ℝ) * |∑ u : (ZMod n)ˣ, (sin (x (i + u) - x i) - sin (y (i + u) - y i))|
      ≤ |K| / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, 2 * dist x y := by
        gcongr
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ => hb u)
    _ = 2 * |K| * dist x y := by
        rw [sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
        field_simp

theorem analyticAt_energy (K : ℝ) (x : ZMod n → ℝ) : AnalyticAt ℝ (energy n K) x := by
  unfold energy
  have hL : ∀ (i : ZMod n) (u : (ZMod n)ˣ),
      AnalyticAt ℝ (fun θ : ZMod n → ℝ => cos (θ (i + u) - θ i)) x := by
    intro i u
    have hlin : AnalyticAt ℝ (fun θ : ZMod n → ℝ => θ (i + u) - θ i) x :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod n => ℝ) (i + u))
        - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod n => ℝ) i).analyticAt x
    exact analyticAt_cos.comp hlin
  refine analyticAt_const.mul ?_
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact Finset.analyticAt_fun_sum _ fun u _ => hL i u

/-! ### The Fréchet derivative at a point, and at twisted states -/

/-- The real Jacobian `(J f)_i = (K/φ) ∑_u w_u (f_{i+u} - f_i)` at the `m`-twisted state. -/
noncomputable def jacR (K : ℝ) (m : ZMod n) (f : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, twistWeight n m u * (f (i + u) - f i)

theorem fderiv_kuramotoField (K : ℝ) (θ f : ZMod n → ℝ) (i : ZMod n) :
    fderiv ℝ (kuramotoField n K) θ f i
      = K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, cos (θ (i + u) - θ i) * (f (i + u) - f i) := by
  have hdiff : DifferentiableAt ℝ (kuramotoField n K) θ :=
    (contDiff_kuramotoField K).differentiable one_ne_zero θ
  have hline : HasDerivAt (fun t : ℝ => θ + t • f) f 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const f).const_add θ
    simpa using this
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hi := (hasDerivAt_pi.mp hcomp) i
  have hk := hasDerivAt_kuramotoField n K θ f i
  have heq : (fun t : ℝ => (kuramotoField n K ∘ fun t => θ + t • f) t i)
      = fun t : ℝ => kuramotoField n K (fun x => θ x + t * f x) i := by
    funext t
    simp only [Function.comp_apply]
    congr 1
  rw [heq] at hi
  exact hi.unique hk

theorem fderiv_kuramotoField_twisted (K : ℝ) (a : ℕ) (f : ZMod n → ℝ) (i : ZMod n) :
    fderiv ℝ (kuramotoField n K) (twisted n a) f i = jacR K (a : ZMod n) f i := by
  rw [fderiv_kuramotoField]
  unfold jacR
  simp only [cos_twisted_diff]

theorem jac_re (K : ℝ) (m : ZMod n) (f : ZMod n → ℂ) (i : ZMod n) :
    (jac n K m f i).re = jacR K m (fun j => (f j).re) i := by
  unfold jac jacR
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine sum_congr rfl fun u _ => ?_
  rw [Complex.re_ofReal_mul, Complex.sub_re]

/-! ### The energy at quarter twists (Theorem 5.6 (i), (ii)) -/

/-- The two-site perturbation `δ = t (e₀ - e₁)`. -/
noncomputable def kick (n : ℕ) (t : ℝ) : ZMod n → ℝ :=
  fun j => t * ((if j = 0 then 1 else 0) - (if j = 1 then 1 else 0))

theorem sum_kick (t : ℝ) : ∑ j, kick n t j = 0 := by
  unfold kick
  rw [← mul_sum, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
  simp

omit [NeZero n] in
theorem sin_kick (h01 : (0 : ZMod n) ≠ 1) (t : ℝ) (j : ZMod n) :
    sin (kick n t j) = sin t * ((if j = 0 then 1 else 0) - (if j = 1 then 1 else 0)) := by
  unfold kick
  by_cases h0 : j = 0
  · subst h0; simp [h01]
  · by_cases h1 : j = 1
    · subst h1; simp [h01.symm, sin_neg]
    · simp [h0, h1]

omit [NeZero n] in
theorem cos_kick (h01 : (0 : ZMod n) ≠ 1) (t : ℝ) (j : ZMod n) :
    cos (kick n t j) = 1 + (cos t - 1) * ((if j = 0 then 1 else 0) + (if j = 1 then 1 else 0)) := by
  unfold kick
  by_cases h0 : j = 0
  · subst h0; simp [h01]
  · by_cases h1 : j = 1
    · subst h1; simp [h01.symm, cos_neg]
    · simp [h0, h1]

theorem sum_ind_mul (g : ZMod n → ℝ) (c : ZMod n) :
    ∑ i : ZMod n, (if i = c then (1 : ℝ) else 0) * g i = g c := by
  simp [ite_mul]

/-- The edge sum of the perturbation along a fixed generator `x`. -/
theorem sum_sin_kick (h01 : (0 : ZMod n) ≠ 1) (t : ℝ) (x : ZMod n) :
    ∑ i : ZMod n, sin (kick n t (i + x) - kick n t i)
      = 2 * sin t * (cos t - 1) * ((if x = -1 then 1 else 0) - (if x = 1 then 1 else 0)) := by
  set d : ZMod n → ℝ := fun j => (if j = 0 then 1 else 0) - (if j = 1 then 1 else 0) with hd
  set e : ZMod n → ℝ := fun j => (if j = 0 then 1 else 0) + (if j = 1 then 1 else 0) with he
  have hs : ∀ j, sin (kick n t j) = sin t * d j := fun j => sin_kick h01 t j
  have hc : ∀ j, cos (kick n t j) = 1 + (cos t - 1) * e j := fun j => cos_kick h01 t j
  have hsum_d : ∑ j : ZMod n, d j = 0 := by
    simp only [hd, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, sub_self]
  have hsum_dx : ∑ i : ZMod n, d (i + x) = 0 := by
    have := Equiv.sum_comp (Equiv.addRight x) d
    simp only [Equiv.coe_addRight] at this
    rw [this]
    exact hsum_d
  have hde : ∑ i : ZMod n, d (i + x) * e i = d x + d (1 + x) := by
    simp only [he, mul_add, sum_add_distrib]
    simp only [mul_comm (d _), sum_ind_mul (fun i => d (i + x))]
    simp
  have hed : ∑ i : ZMod n, e (i + x) * d i = e x - e (1 + x) := by
    simp only [hd, mul_sub, sum_sub_distrib]
    simp only [mul_comm (e _), sum_ind_mul (fun i => e (i + x))]
    simp
  have expand : ∀ i, sin (kick n t (i + x) - kick n t i)
      = sin t * d (i + x) + sin t * (cos t - 1) * (d (i + x) * e i)
        - sin t * d i - sin t * (cos t - 1) * (e (i + x) * d i) := by
    intro i
    rw [sin_sub, hs, hs, hc, hc]
    ring
  rw [sum_congr rfl fun i _ => expand i, sum_sub_distrib, sum_sub_distrib, sum_add_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, hsum_dx, hde, hsum_d, hed]
  have e1 : (1 + x = 0) ↔ x = -1 := by
    constructor
    · intro h; linear_combination h
    · intro h; rw [h]; ring
  have e2 : (1 + x = 1) ↔ x = 0 := by
    constructor
    · intro h; linear_combination h
    · intro h; rw [h]; ring
  simp only [hd, he, e1, e2]
  by_cases h0 : x = 0
  · subst h0
    have : (0 : ZMod n) ≠ -1 := by
      intro h; apply h01; linear_combination -h
    simp [h01, this]
  · by_cases h1 : x = 1
    · subst h1
      simp [h01.symm]
      split_ifs <;> ring
    · simp [h0, h1]
      split_ifs <;> ring

/-- The sine of the phase lag along generator `u` at the `a`-twisted state. -/
noncomputable def sigma (n : ℕ) [NeZero n] (a : ℕ) (u : ZMod n) : ℝ :=
  (ZMod.stdAddChar ((a : ZMod n) * u) : ℂ).im

theorem sigma_neg (a : ℕ) (u : ZMod n) : sigma n a (-u) = -sigma n a u := by
  unfold sigma
  rw [mul_neg, ← conj_stdAddChar, Complex.conj_im]

/-- **Theorem 5.6 (i).**  If every edge weight vanishes, the energy of the twisted state is `0`. -/
theorem energy_twisted_eq_zero (K : ℝ) (a : ℕ) (hz : ∀ u, twistWeight n (a : ZMod n) u = 0) :
    energy n K (twisted n a) = 0 := by
  unfold energy
  simp [cos_twisted_diff, hz]

/-- **Theorem 5.6 (ii), general form.**  If every edge weight at the `a`-twisted state vanishes,
then `E(θ + t(e₀ - e₁)) = (2K/φ(n)) σ sin t (1 - cos t)` with `σ = sin(2πa/n)`. -/
theorem energy_twisted_kick (K : ℝ) (a : ℕ) (hz : ∀ u, twistWeight n (a : ZMod n) u = 0)
    (h01 : (0 : ZMod n) ≠ 1) (t : ℝ) :
    energy n K (twisted n a + kick n t)
      = 2 * K / (Nat.totient n : ℝ) * sigma n a 1 * sin t * (1 - cos t) := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  have hterm : ∀ (i : ZMod n) (u : (ZMod n)ˣ),
      cos ((twisted n a + kick n t) (i + u) - (twisted n a + kick n t) i)
        = -(sigma n a u * sin (kick n t (i + u) - kick n t i)) := by
    intro i u
    have e : (twisted n a + kick n t) (i + u) - (twisted n a + kick n t) i
        = (twisted n a (i + u) - twisted n a i) + (kick n t (i + u) - kick n t i) := by
      simp only [Pi.add_apply]; ring
    rw [e, cos_add, cos_twisted_diff, hz, sin_twisted_diff]
    unfold sigma
    ring
  have hu : ∀ u : (ZMod n)ˣ, ((u : ZMod n) = -1 ↔ u = -1) := fun u => by
    rw [Units.ext_iff, Units.val_neg, Units.val_one]
  have hu1 : ∀ u : (ZMod n)ˣ, ((u : ZMod n) = 1 ↔ u = 1) := fun u => by
    rw [Units.ext_iff, Units.val_one]
  set C := 2 * sin t * (cos t - 1) with hC
  have hsum : ∑ i : ZMod n, ∑ u : (ZMod n)ˣ,
      cos ((twisted n a + kick n t) (i + u) - (twisted n a + kick n t) i)
        = -(C * (sigma n a (-1) - sigma n a 1)) := by
    rw [sum_congr rfl fun i _ => sum_congr rfl fun u _ => hterm i u]
    simp only [sum_neg_distrib]
    rw [sum_comm]
    congr 1
    have h1 : ∀ u : (ZMod n)ˣ, ∑ i : ZMod n, sigma n a u * sin (kick n t (i + u) - kick n t i)
        = C * ((if u = -1 then sigma n a (-1) else 0) - (if u = 1 then sigma n a 1 else 0)) := by
      intro u
      rw [← mul_sum, sum_sin_kick h01]
      simp only [hu, hu1]
      rcases em (u = -1) with ha | ha <;> rcases em (u = 1) with hb | hb
      · have e1 : (u : ZMod n) = -1 := (hu u).mpr ha
        have e2 : (u : ZMod n) = 1 := (hu1 u).mpr hb
        have e3 : sigma n a (-1) = sigma n a 1 := by rw [← e1, e2]
        rw [if_pos ha, if_pos hb, if_pos ha, if_pos hb, e3]
        ring
      · have e1 : (u : ZMod n) = -1 := (hu u).mpr ha
        rw [if_pos ha, if_neg hb, if_pos ha, if_neg hb, e1]
        ring
      · have e2 : (u : ZMod n) = 1 := (hu1 u).mpr hb
        rw [if_neg ha, if_pos hb, if_neg ha, if_pos hb, e2]
        ring
      · rw [if_neg ha, if_neg hb, if_neg ha, if_neg hb]
        ring
    rw [sum_congr rfl fun u _ => h1 u, ← mul_sum, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
    simp
  unfold energy
  rw [hsum, sigma_neg, hC]
  field_simp
  ring

omit [NeZero n] in
theorem natCast_quarter (h4 : 4 ∣ n) :
    (((3 * (n / 4) : ℕ)) : ZMod n) = -((n / 4 : ℕ) : ZMod n) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← Nat.cast_add]
  have e : 3 * (n / 4) + n / 4 = n := by
    have := Nat.div_mul_cancel h4
    omega
  rw [e, ZMod.natCast_self]

theorem sigma_quarter (h4 : 4 ∣ n) : sigma n (n / 4) 1 = 1 := by
  unfold sigma
  rw [mul_one, stdAddChar_natCast_im]
  obtain ⟨c, hc⟩ := h4
  have hc0 : (c : ℝ) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; exact NeZero.ne n (by simpa using hc)
    exact_mod_cast this
  have hdiv : n / 4 = c := by rw [hc]; exact Nat.mul_div_cancel_left c (by norm_num)
  rw [hdiv, hc]
  push_cast
  have : 2 * π * c / (4 * c) = π / 2 := by field_simp; ring
  rw [this, sin_pi_div_two]

theorem sigma_three_quarter (h4 : 4 ∣ n) : sigma n (3 * (n / 4)) 1 = -1 := by
  have h : sigma n (3 * (n / 4)) 1 = sigma n (n / 4) (-1) := by
    unfold sigma
    rw [natCast_quarter h4, neg_mul, mul_neg]
  rw [h, sigma_neg, sigma_quarter h4]

theorem twistWeight_three_quarter (h4 : 4 ∣ n) (u : (ZMod n)ˣ) :
    twistWeight n ((3 * (n / 4) : ℕ) : ZMod n) u = 0 := by
  rw [natCast_quarter h4, twistWeight_neg, twistWeight_quarter h4]

theorem zero_ne_one_of_four_dvd (h4 : 4 ∣ n) : (0 : ZMod n) ≠ 1 := by
  have : 1 < n := by
    obtain ⟨c, hc⟩ := h4
    have := NeZero.ne n
    omega
  haveI : Fact (1 < n) := ⟨this⟩
  exact zero_ne_one

/-- **Theorem 5.6 (ii) for `m = n/4`.** -/
theorem energy_quarter_kick (h4 : 4 ∣ n) (K t : ℝ) :
    energy n K (twisted n (n / 4) + kick n t)
      = 2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t) := by
  rw [energy_twisted_kick K _ (fun u => twistWeight_quarter h4 u) (zero_ne_one_of_four_dvd h4),
    sigma_quarter h4]
  ring

/-- **Theorem 5.6 (ii) for `m = 3n/4`.** -/
theorem energy_three_quarter_kick (h4 : 4 ∣ n) (K t : ℝ) :
    energy n K (twisted n (3 * (n / 4)) + kick n t)
      = -(2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t)) := by
  rw [energy_twisted_kick K _ (fun u => twistWeight_three_quarter h4 u)
    (zero_ne_one_of_four_dvd h4), sigma_three_quarter h4]
  ring

end ArithmeticDynamics
