/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XVI: nonlinear stability conclusions (Theorems 5.4, 5.5, 5.6 (iii), Corollary 5.7).

Three classical theorems of dynamical systems are used as explicit hypotheses.  Each is stated
for *every* vector field on `ℝ^{ℤ/n}` satisfying the standard assumptions, so each is a genuine
classical theorem and not a statement tailored to the Kuramoto model:
* `LyapunovIndirectStability`  — Lyapunov's indirect method (stability), on an invariant level set;
* `LyapunovIndirectInstability` — Lyapunov's instability theorem by first approximation;
* `AbsilKurdyka` — Absil–Kurdyka (2006): for an analytic energy, a stable equilibrium of the
  gradient flow is a local minimum.
-/
import Mathlib
import ArithmeticDynamics.Energy

namespace ArithmeticDynamics

open Finset Real Filter Topology

variable {n : ℕ} [NeZero n]

/-! ### Dynamical notions (Euclidean norm `sqNorm`) -/

/-- `x` is a solution of `ẋ = F(x)` defined for all times. -/
def IsSolution (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (x : ℝ → ZMod n → ℝ) : Prop :=
  ∀ t, HasDerivAt x (F (x t)) t

/-- Lyapunov stability of an equilibrium `xs`. -/
def LyapunovStable (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, IsSolution F x → sqNorm (x 0 - xs) < δ →
    ∀ t ≥ 0, sqNorm (x t - xs) < ε

/-- Local exponential stability with rate `ρ` on the level set `∑ x = ∑ xs`
("modulo rotation" for the Kuramoto model). -/
def ExpStableOnLevel (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) (ρ : ℝ) : Prop :=
  ∃ δ > 0, ∀ x, IsSolution F x → ∑ j, x 0 j = ∑ j, xs j → sqNorm (x 0 - xs) < δ →
    ∀ t ≥ 0, sqNorm (x t - xs) ≤ Real.exp (-2 * ρ * t) * sqNorm (x 0 - xs)

/-! ### The classical theorems, as hypotheses -/

variable (n) in
/-- **Lyapunov's indirect method (stability).**  For a `C¹`, globally Lipschitz field with zero
sum and an equilibrium whose linearisation is `≤ -r` on sum-zero vectors, the equilibrium is
exponentially stable with every rate `r' < r` on its level set. -/
def LyapunovIndirectStability : Prop :=
  ∀ (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) (r : ℝ),
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) → F xs = 0 → (∀ x, ∑ j, F x j = 0) → 0 < r →
    (∀ w : ZMod n → ℝ, ∑ j, w j = 0 → ∑ j, fderiv ℝ F xs w j * w j ≤ -r * sqNorm w) →
    ∀ r', 0 < r' → r' < r → ExpStableOnLevel F xs r'

variable (n) in
/-- **Lyapunov's instability theorem by first approximation.**  A real eigenvalue `μ > 0` of the
linearisation at an equilibrium of a `C¹`, globally Lipschitz field makes it unstable. -/
def LyapunovIndirectInstability : Prop :=
  ∀ (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs v : ZMod n → ℝ) (μ : ℝ),
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) → F xs = 0 → v ≠ 0 →
    fderiv ℝ F xs v = μ • v → 0 < μ → ¬ LyapunovStable F xs

variable (n) in
/-- **Absil–Kurdyka.**  If `E` is real analytic and `F = -∇E` is `C¹` and globally Lipschitz,
then every Lyapunov-stable equilibrium of `ẋ = F(x)` is a local minimum of `E`. -/
def AbsilKurdyka : Prop :=
  ∀ (E : (ZMod n → ℝ) → ℝ) (F : (ZMod n → ℝ) → (ZMod n → ℝ)),
    (∀ x, AnalyticAt ℝ E x) →
    (∀ x v, HasDerivAt (fun t : ℝ => E (x + t • v)) (-∑ j, F x j * v j) 0) →
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) →
    ∀ xs, F xs = 0 → LyapunovStable F xs → IsLocalMin E xs

/-! ### Jacobians at the hexagonal and synchronous states -/

theorem kuramotoField_twisted_eq (K : ℝ) (a : ℕ) : kuramotoField n K (twisted n a) = 0 :=
  funext fun i => kuramotoField_twisted n K a i

theorem jacR_hex (h6 : 6 ∣ n) (K : ℝ) (f : ZMod n → ℝ) (i : ZMod n) :
    jacR K ((n / 6 : ℕ) : ZMod n) f i = -(K / (2 * (Nat.totient n : ℝ))) * lapR f i := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  unfold jacR lapR
  simp only [twistWeight_hex h6]
  rw [← mul_sum, sum_sub_distrib, sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  field_simp
  ring

theorem twistWeight_zero (u : (ZMod n)ˣ) : twistWeight n 0 u = 1 := by
  unfold twistWeight
  simp

theorem jacR_sync (K : ℝ) (f : ZMod n → ℝ) (i : ZMod n) :
    jacR K 0 f i = -(K / (Nat.totient n : ℝ)) * lapR f i := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  unfold jacR lapR
  simp only [twistWeight_zero, one_mul]
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  ring

theorem lapEig_ge_half (k : ZMod n) (hk : k ≠ 0) : (Nat.totient n : ℝ) / 2 ≤ lapEig n k := by
  have h := r_le_half_of_one_lt (one_lt_addOrderOf hk)
  have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  unfold lapEig
  nlinarith

theorem quad_upper_aux : ∀ k : ZMod n, k ≠ 0 → lapEig n k ≤ ∑ k', |lapEig n k'| := fun k _ =>
  (le_abs_self _).trans (single_le_sum (f := fun k' => |lapEig n k'|)
    (fun _ _ => abs_nonneg _) (mem_univ k))

/-- The linearisation at the hexagonal state is `≤ -K/4` on sum-zero vectors. -/
theorem quad_hex (h6 : 6 ∣ n) {K : ℝ} (hK : 0 ≤ K) (w : ZMod n → ℝ) (hw : ∑ j, w j = 0) :
    ∑ j, jacR K ((n / 6 : ℕ) : ZMod n) w j * w j ≤ -(K / 4) * sqNorm w := by
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hq := (quadForm_bounds w hw lapEig_ge_half quad_upper_aux).1
  simp_rw [jacR_hex h6, mul_assoc, ← mul_sum]
  have hc : 0 ≤ K / (2 * (Nat.totient n : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  have e : K / (2 * (Nat.totient n : ℝ)) * ((Nat.totient n : ℝ) / 2 * sqNorm w)
      = K / 4 * sqNorm w := by field_simp; ring
  linarith

/-- The linearisation at the synchronous state is `≤ -K/2` on sum-zero vectors. -/
theorem quad_sync {K : ℝ} (hK : 0 ≤ K) (w : ZMod n → ℝ) (hw : ∑ j, w j = 0) :
    ∑ j, jacR K 0 w j * w j ≤ -(K / 2) * sqNorm w := by
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hq := (quadForm_bounds w hw lapEig_ge_half quad_upper_aux).1
  simp_rw [jacR_sync, mul_assoc, ← mul_sum]
  have hc : 0 ≤ K / (Nat.totient n : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  have e : K / (Nat.totient n : ℝ) * ((Nat.totient n : ℝ) / 2 * sqNorm w) = K / 2 * sqNorm w := by
    field_simp
  linarith

/-! ### Theorem 5.5: exponential stability of the hexagonal and synchronous states -/

/-- **Theorem 5.5.**  For `6 ∣ n` the hexagonal state is exponentially stable modulo rotation
with every rate `r' < K/4`. -/
theorem hex_expStable (hL : LyapunovIndirectStability n) (h6 : 6 ∣ n) {K : ℝ} (hK : 0 < K)
    {r' : ℝ} (hr' : 0 < r') (hr : r' < K / 4) :
    ExpStableOnLevel (kuramotoField n K) (twisted n (n / 6)) r' :=
  hL _ _ (K / 4) (contDiff_kuramotoField K) (lipschitz_kuramotoField K)
    (kuramotoField_twisted_eq K _) (sum_kuramotoField K) (by positivity)
    (fun w hw => by
      simp_rw [fderiv_kuramotoField_twisted]
      exact quad_hex h6 hK.le w hw) r' hr' hr

/-- **Theorem 5.5 (synchronous state).**  The synchronous state is exponentially stable modulo
rotation with every rate `r' < K/2`. -/
theorem sync_expStable (hL : LyapunovIndirectStability n) {K : ℝ} (hK : 0 < K)
    {r' : ℝ} (hr' : 0 < r') (hr : r' < K / 2) :
    ExpStableOnLevel (kuramotoField n K) (twisted n 0) r' :=
  hL _ _ (K / 2) (contDiff_kuramotoField K) (lipschitz_kuramotoField K)
    (kuramotoField_twisted_eq K _) (sum_kuramotoField K) (by positivity)
    (fun w hw => by
      simp_rw [fderiv_kuramotoField_twisted]
      have : ((0 : ℕ) : ZMod n) = 0 := Nat.cast_zero
      rw [this]
      exact quad_sync hK.le w hw) r' hr' hr

/-! ### Theorem 5.5: the second hexagonal state `m = 5n/6` -/

omit [NeZero n] in
theorem natCast_five_sixth (h6 : 6 ∣ n) :
    ((5 * (n / 6) : ℕ) : ZMod n) = -((n / 6 : ℕ) : ZMod n) := by
  rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
  have e : 5 * (n / 6) + n / 6 = n := by omega
  rw [e, ZMod.natCast_self]

/-- At the hexagonal state `m = 5n/6` every edge weight is again `1/2`. -/
theorem twistWeight_hex_five (h6 : 6 ∣ n) (u : (ZMod n)ˣ) :
    twistWeight n ((5 * (n / 6) : ℕ) : ZMod n) u = 1 / 2 := by
  rw [natCast_five_sixth h6, twistWeight_neg, twistWeight_hex h6]

/-- **Theorem 5.5 for `m = 5n/6`.**  The Jacobian at `m = 5n/6` equals the Jacobian at `m = n/6`,
namely `-(K/(2φ(n)))` times the Laplacian of `X_n`. -/
theorem jac_hex_five (h6 : 6 ∣ n) (K : ℝ) (f : ZMod n → ℂ) (i : ZMod n) :
    jac n K ((5 * (n / 6) : ℕ) : ZMod n) f i
      = -((K / (2 * (Nat.totient n : ℝ)) : ℝ) : ℂ) * lap n f i := by
  rw [← jac_hex h6]
  unfold jac
  simp only [twistWeight_hex_five h6, twistWeight_hex h6]

/-- **Theorem 5.5 for `m = 5n/6`.**  For `6 ∣ n` the hexagonal state `θ_j = -jπ/3` (that is,
`m = 5n/6`) is exponentially stable modulo rotation with every rate `r' < K/4`. -/
theorem hex_expStable_five (hL : LyapunovIndirectStability n) (h6 : 6 ∣ n) {K : ℝ} (hK : 0 < K)
    {r' : ℝ} (hr' : 0 < r') (hr : r' < K / 4) :
    ExpStableOnLevel (kuramotoField n K) (twisted n (5 * (n / 6))) r' := by
  have hJ : ∀ (f : ZMod n → ℝ) (i : ZMod n),
      jacR K ((5 * (n / 6) : ℕ) : ZMod n) f i = jacR K ((n / 6 : ℕ) : ZMod n) f i := by
    intro f i
    unfold jacR
    simp only [twistWeight_hex_five h6, twistWeight_hex h6]
  exact hL _ _ (K / 4) (contDiff_kuramotoField K) (lipschitz_kuramotoField K)
    (kuramotoField_twisted_eq K _) (sum_kuramotoField K) (by positivity)
    (fun w hw => by
      simp_rw [fderiv_kuramotoField_twisted, hJ]
      exact quad_hex h6 hK.le w hw) r' hr' hr

/-! ### Theorem 5.5: the linear rates are exact -/

omit [NeZero n] in
theorem twoSmallest_two_three (h6 : 6 ∣ n) : TwoSmallest n 2 3 := by
  refine ⟨Nat.prime_two, Nat.prime_three, dvd_trans (by norm_num) h6, dvd_trans (by norm_num) h6,
    by norm_num, fun ℓ hℓ _ => hℓ.two_le, fun ℓ hℓ _ hne => ?_⟩
  have := hℓ.two_le
  omega

/-- **Theorem 5.5, spectrum.**  The eigenvalues `-(K/2)(1 - r(ord k))`, `k ≠ 0`, of the hexagonal
Jacobian lie in `[-K, -K/4]`, and `-K/4` is attained exactly at the residues of order `6`. -/
theorem hex_spectrum (h6 : 6 ∣ n) {K : ℝ} (hK : 0 < K) (k : ZMod n) (hk : k ≠ 0) :
    -K ≤ -(K / 2) * (1 - r (addOrderOf k)) ∧ -(K / 2) * (1 - r (addOrderOf k)) ≤ -(K / 4) ∧
      (-(K / 2) * (1 - r (addOrderOf k)) = -(K / 4) ↔ addOrderOf k = 6) := by
  have hM := one_lt_addOrderOf hk
  have hlo : -1 ≤ r (addOrderOf k) := by
    have h1 := abs_r_le (addOrderOf k)
    have h2 : (1 : ℝ) ≤ (Nat.totient (addOrderOf k) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have h3 : 1 / (Nat.totient (addOrderOf k) : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact h2
    linarith [neg_abs_le (r (addOrderOf k))]
  have hhi := r_le_half_of_one_lt hM
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have key := r_eq_max_iff (twoSmallest_two_three h6) hM (addOrderOf_dvd_self k)
  norm_num at key
  constructor
  · intro h
    have : r (addOrderOf k) = 1 / 2 := by
      have hK2 : K / 2 ≠ 0 := by positivity
      field_simp at h
      linarith
    exact key.mp this
  · intro h
    rw [key.mpr h]
    ring

/-- **Theorem 5.5, synchronous state.**  At `m = 0` the Jacobian is `-(K/φ) L`, with eigenvalues
`-K(1 - r(ord k)) ≤ -K/2` for `k ≠ 0`; for `6 ∣ n` the value `-K/2` is attained. -/
theorem jac_sync_chi (K : ℝ) (k i : ZMod n) :
    jac n K 0 (chi n k) i = ((-K * (1 - r (addOrderOf k)) : ℝ) : ℂ) * chi n k i := by
  rw [jac_chi, zero_add, zero_sub, addOrderOf_neg, addOrderOf_zero, r_one]
  congr 2
  ring

theorem sync_rate (K : ℝ) (hK : 0 ≤ K) (k : ZMod n) (hk : k ≠ 0) :
    -K * (1 - r (addOrderOf k)) ≤ -(K / 2) := by
  have := r_le_half_of_one_lt (one_lt_addOrderOf hk)
  nlinarith

theorem sync_rate_attained (h6 : 6 ∣ n) (K : ℝ) :
    -K * (1 - r (addOrderOf ((n / 6 : ℕ) : ZMod n))) = -(K / 2) := by
  rw [addOrderOf_natCast_div h6, r_six]
  ring

/-! ### Theorem 5.4 (c): nonlinear instability -/

theorem chi_zero (k : ZMod n) : chi n k 0 = 1 := by
  unfold chi
  simp

/-- **Theorem 5.4 (c), nonlinear form.**  If `m ≠ 0` has order `∉ {4, 6}`, the `m`-twisted state
is (Lyapunov) unstable. -/
theorem twisted_unstable_nonlinear (hI : LyapunovIndirectInstability n) {K : ℝ} (hK : 0 < K)
    {a : ℕ} (hm : (a : ZMod n) ≠ 0) (h4 : addOrderOf (a : ZMod n) ≠ 4)
    (h6 : addOrderOf (a : ZMod n) ≠ 6) :
    ¬ LyapunovStable (kuramotoField n K) (twisted n a) := by
  set m : ZMod n := (a : ZMod n)
  set v : ZMod n → ℝ := fun j => (chi n m j).re with hv
  set μ := K * g (addOrderOf m)
  have hμ : 0 < μ := (twisted_unstable hK hm h4 h6).2
  refine hI _ _ v μ (contDiff_kuramotoField K) (lipschitz_kuramotoField K)
    (kuramotoField_twisted_eq K a) ?_ ?_ hμ
  · intro h
    have := congrFun h 0
    simp [hv, chi_zero] at this
  · funext i
    rw [Pi.smul_apply, smul_eq_mul, fderiv_kuramotoField_twisted]
    have h := congrArg Complex.re (jac_chi_self K m i)
    rw [jac_re, Complex.re_ofReal_mul] at h
    exact h

/-! ### Theorem 5.6 (iii): quarter twists are not minima, hence unstable -/

theorem norm_kick_le (τ : ℝ) (hτ : 0 ≤ τ) : ‖kick n (-τ)‖ ≤ τ := by
  refine (pi_norm_le_iff_of_nonneg hτ).mpr fun j => ?_
  unfold kick
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hτ]
  have : |(if j = 0 then (1 : ℝ) else 0) - (if j = 1 then 1 else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  nlinarith

theorem norm_kick_le' (τ : ℝ) (hτ : 0 ≤ τ) : ‖kick n τ‖ ≤ τ := by
  have := norm_kick_le (n := n) τ hτ
  have e : kick n τ = -kick n (-τ) := by
    funext j; unfold kick; simp only [Pi.neg_apply]; ring
  rwa [e, norm_neg]

theorem sin_mul_one_sub_cos_pos {τ : ℝ} (h0 : 0 < τ) (h1 : τ ≤ 1) :
    0 < sin τ * (1 - cos τ) := by
  have hπ : τ < π := lt_of_le_of_lt h1 (by linarith [pi_gt_three])
  have hs := sin_pos_of_pos_of_lt_pi h0 hπ
  have hc : cos τ < 1 := by
    have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0
    rwa [cos_zero] at this
  exact mul_pos hs (by linarith)

/-- A local minimum would be beaten by a small two-site kick of energy `< 0 = E(θ)`. -/
theorem not_isLocalMin_of_kick {K : ℝ} (hK : 0 < K) (θ : ZMod n → ℝ) (hE0 : energy n K θ = 0)
    (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hform : ∀ t, energy n K (θ + kick n t)
      = s * (2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t))) :
    ¬ IsLocalMin (energy n K) θ := by
  intro hmin
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hmin
  set τ := min (ε / 2) 1 with hτ
  have hτ0 : 0 < τ := lt_min (by positivity) one_pos
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτε : τ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hpos := sin_mul_one_sub_cos_pos hτ0 hτ1
  have hc : 0 < 2 * K / (Nat.totient n : ℝ) := by positivity
  set t := -s * τ with ht
  have hdist : dist (θ + kick n t) θ < ε := by
    rw [dist_eq_norm, add_sub_cancel_left]
    rcases hs with rfl | rfl
    · have : t = -τ := by rw [ht]; ring
      rw [this]
      exact lt_of_le_of_lt (norm_kick_le τ hτ0.le) hτε
    · have : t = τ := by rw [ht]; ring
      rw [this]
      exact lt_of_le_of_lt (norm_kick_le' τ hτ0.le) hτε
  have hle := hball hdist
  rw [hE0, hform t] at hle
  have hval : s * (2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t))
      = -(2 * K / (Nat.totient n : ℝ) * (sin τ * (1 - cos τ))) := by
    rcases hs with rfl | rfl
    · have : t = -τ := by rw [ht]; ring
      rw [this, sin_neg, cos_neg]; ring
    · have : t = τ := by rw [ht]; ring
      rw [this]; ring
  rw [hval] at hle
  have := mul_pos hc hpos
  linarith

/-- **Theorem 5.6 (iii).**  The quarter twist `m = n/4` is not a local minimum of the energy. -/
theorem quarter_not_isLocalMin (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ IsLocalMin (energy n K) (twisted n (n / 4)) :=
  not_isLocalMin_of_kick hK _
    (energy_twisted_eq_zero K _ fun u => twistWeight_quarter h4 u) 1 (Or.inl rfl)
    (fun t => by rw [energy_quarter_kick h4, one_mul])

/-- **Theorem 5.6 (iii).**  The quarter twist `m = 3n/4` is not a local minimum of the energy. -/
theorem three_quarter_not_isLocalMin (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ IsLocalMin (energy n K) (twisted n (3 * (n / 4))) :=
  not_isLocalMin_of_kick hK _
    (energy_twisted_eq_zero K _ fun u => twistWeight_three_quarter h4 u) (-1) (Or.inr rfl)
    (fun t => by rw [energy_three_quarter_kick h4]; ring)

/-- **Theorem 5.6 (iii).**  Under Absil–Kurdyka, the quarter twists are unstable. -/
theorem quarter_unstable (hAK : AbsilKurdyka n) (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ LyapunovStable (kuramotoField n K) (twisted n (n / 4)) ∧
      ¬ LyapunovStable (kuramotoField n K) (twisted n (3 * (n / 4))) := by
  constructor
  · intro hst
    exact quarter_not_isLocalMin h4 hK
      (hAK (energy n K) (kuramotoField n K) (analyticAt_energy K) (energy_hasDerivAt_line K)
        (contDiff_kuramotoField K) (lipschitz_kuramotoField K) _
        (kuramotoField_twisted_eq K _) hst)
  · intro hst
    exact three_quarter_not_isLocalMin h4 hK
      (hAK (energy n K) (kuramotoField n K) (analyticAt_energy K) (energy_hasDerivAt_line K)
        (contDiff_kuramotoField K) (lipschitz_kuramotoField K) _
        (kuramotoField_twisted_eq K _) hst)

/-! ### Corollary 5.7: the role of six -/

/-- **Corollary 5.7.**  For `m ≠ 0`, the `m`-twisted state is linearly stable (every non-trivial
character is an eigenvector with a negative eigenvalue) iff `m` has order `6`. -/
theorem linearly_stable_iff {K : ℝ} (hK : 0 < K) {m : ZMod n} (hm : m ≠ 0) :
    (∀ k : ZMod n, k ≠ 0 → ∃ ev : ℝ, ev < 0 ∧ ∀ i, jac n K m (chi n k) i = (ev : ℂ) * chi n k i)
      ↔ addOrderOf m = 6 := by
  constructor
  · intro h
    by_contra h6
    obtain ⟨ev, hev, hjac⟩ := h m hm
    have h0 := hjac 0
    rw [chi_zero, mul_one] at h0
    by_cases h4 : addOrderOf m = 4
    · rw [(twisted_classification hK hm).2.1 h4] at h0
      have : ev = 0 := by exact_mod_cast h0.symm
      linarith
    · rw [jac_chi_self, chi_zero, mul_one] at h0
      have : K * g (addOrderOf m) = ev := by exact_mod_cast h0
      have := (twisted_unstable hK hm h4 h6).2
      linarith
  · intro h6 k hk
    obtain ⟨ev, hev, hjac⟩ := (twisted_classification hK hm).1 h6 k hk
    exact ⟨ev, by linarith, hjac⟩

/-- **Corollary 5.7.**  `X_n` has a non-zero twist of order `6` iff `6 ∣ n`. -/
theorem exists_order_six_iff : (∃ m : ZMod n, m ≠ 0 ∧ addOrderOf m = 6) ↔ 6 ∣ n := by
  constructor
  · rintro ⟨m, _, h⟩
    exact h ▸ addOrderOf_dvd_self m
  · intro h6
    exact ⟨_, natCast_div_ne_zero h6 (by norm_num), addOrderOf_natCast_div h6⟩

end ArithmeticDynamics
