/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XII: consensus dynamics on `X_n` — the discrete iteration with its exact contraction
(Lemma 4.1, Theorem 4.3), the optimal step (4.6), the universal bound and iteration count
(Corollary 4.5), the natural step (Proposition 4.7), and the continuous-time flow (Remark 4.8).
-/
import Mathlib
import ArithmeticDynamics.Fourier
import ArithmeticDynamics.Multiplicity

namespace ArithmeticDynamics

open Finset ArithmeticFunction

variable {n : ℕ} [NeZero n]

/-- The average `x̄ = (1/n) ∑ x_j`. -/
noncomputable def avg (x : ZMod n → ℝ) : ℝ := (∑ j, x j) / n

/-- The consensus error `x - x̄ 1`. -/
noncomputable def err (x : ZMod n → ℝ) : ZMod n → ℝ := fun j => x j - avg x

/-- One step of the consensus iteration `x ↦ (I - ε L) x` on `X_n`. -/
noncomputable def step (ε : ℝ) (x : ZMod n → ℝ) : ZMod n → ℝ := fun j => x j - ε * lapR x j

theorem sum_err (x : ZMod n → ℝ) : ∑ j, err x j = 0 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  unfold err avg
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  field_simp
  ring

theorem lapR_sub_const (x : ZMod n → ℝ) (c : ℝ) : lapR (fun j => x j - c) = lapR x := by
  funext i
  unfold lapR
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  ring

theorem sum_step (ε : ℝ) (x : ZMod n → ℝ) : ∑ j, step ε x j = ∑ j, x j := by
  unfold step
  rw [sum_sub_distrib, ← mul_sum, sum_lapR, mul_zero, sub_zero]

theorem avg_step (ε : ℝ) (x : ZMod n → ℝ) : avg (step ε x) = avg x := by
  unfold avg
  rw [sum_step]

theorem err_step (ε : ℝ) (x : ZMod n → ℝ) : err (step ε x) = step ε (err x) := by
  funext j
  unfold err
  rw [avg_step]
  change step ε x j - avg x = step ε (fun j => x j - avg x) j
  unfold step
  rw [lapR_sub_const]
  ring

/-- **Lemma 4.1 / Theorem 4.3, the norm estimate.**  If `|1 - ε λ(k)| ≤ ρ` for all `k ≠ 0`, then
`‖x(t) - x̄ 1‖² ≤ ρ^{2t} ‖x(0) - x̄ 1‖²` for the iteration `x(t+1) = (I - εL) x(t)`. -/
theorem sqNorm_err_iterate {ε ρ : ℝ} (hρ : ∀ k : ZMod n, k ≠ 0 → |1 - ε * lapEig n k| ≤ ρ)
    (x : ZMod n → ℝ) (t : ℕ) :
    sqNorm (err ((step ε)^[t] x)) ≤ (ρ ^ 2) ^ t * sqNorm (err x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', err_step, pow_succ]
    calc sqNorm (step ε (err ((step ε)^[t] x)))
        ≤ ρ ^ 2 * sqNorm (err ((step ε)^[t] x)) := sqNorm_step_le _ (sum_err _) hρ
      _ ≤ ρ ^ 2 * ((ρ ^ 2) ^ t * sqNorm (err x)) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = (ρ ^ 2) ^ t * ρ ^ 2 * sqNorm (err x) := by ring

theorem r_le_half_of_one_lt {M : ℕ} (hM : 1 < M) : r M ≤ 1 / 2 := by
  by_cases h2 : M = 2
  · subst h2
    rw [r_two]
    norm_num
  · exact (abs_le.mp (abs_r_le_half (by omega))).2

/-- **Theorem 4.3, dynamical form.**  If `ρ` is the optimal rate of `X_n` (`IsRate n ρ`), then the
iteration with the optimal step `ε* = 2/(λ₂ + λ_max)` satisfies
`‖x(t) - x̄ 1‖² ≤ ρ^{2t} ‖x(0) - x̄ 1‖²` for every initial vector. -/
theorem consensus_of_isRate {ρ : ℝ} (h : IsRate n ρ) :
    ∃ ε > 0, ∀ (x : ZMod n → ℝ) (t : ℕ),
      sqNorm (err ((step ε)^[t] x)) ≤ (ρ ^ 2) ^ t * sqNorm (err x) := by
  obtain ⟨rmax, rmin, hmax, hmin, rfl⟩ := h
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨M, hMn, hM, hrM⟩ := hmax.1
  have hrmax : rmax ≤ 1 / 2 := hrM ▸ r_le_half_of_one_lt hM
  have hle : rmin ≤ rmax := hmin.2 hmax.1
  set a := (Nat.totient n : ℝ) * (1 - rmax) with ha
  set b := (Nat.totient n : ℝ) * (1 - rmin) with hb
  have ha0 : 0 < a := mul_pos hφ (by linarith)
  have hab : a ≤ b := mul_le_mul_of_nonneg_left (by linarith) hφ.le
  have hs : 0 < a + b := by linarith
  refine ⟨2 / (a + b), by positivity, fun x t => ?_⟩
  have hrate : rateOf rmax rmin * (a + b) = b - a := by
    have hd : (2 : ℝ) - rmax - rmin ≠ 0 := by
      have : (0 : ℝ) < 2 - rmax - rmin := by linarith
      exact this.ne'
    unfold rateOf
    rw [ha, hb]
    field_simp
    ring
  refine sqNorm_err_iterate (fun k hk => ?_) x t
  have hmem : r (addOrderOf k) ∈ DivSet n := (mem_divSet_iff _).mpr ⟨k, hk, rfl⟩
  have hlo : a ≤ lapEig n k := mul_le_mul_of_nonneg_left (by linarith [hmax.2 hmem]) hφ.le
  have hhi : lapEig n k ≤ b := mul_le_mul_of_nonneg_left (by linarith [hmin.2 hmem]) hφ.le
  exact contraction_of_opt_step hs (by field_simp) hrate hlo hhi

/-- Every `n ≥ 2` has an optimal rate. -/
theorem exists_isRate {m : ℕ} (hm : 2 ≤ m) : ∃ ρ : ℝ, IsRate m ρ := by
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      subst this
      rw [pow_one]
      exact ⟨0, isRate_prime hp⟩
    · exact ⟨_, isRate_prime_pow hp hk2⟩
  · obtain ⟨q, hts⟩ := exists_twoSmallest hm hpp
    exact ⟨_, isRate_of_twoSmallest hm hts⟩

theorem isRate_nonneg {m : ℕ} {ρ : ℝ} (h : IsRate m ρ) : 0 ≤ ρ := by
  obtain ⟨rmax, rmin, hmax, hmin, rfl⟩ := h
  obtain ⟨M, _, hM, hrM⟩ := hmax.1
  have hrmax : rmax ≤ 1 / 2 := hrM ▸ r_le_half_of_one_lt hM
  have hle : rmin ≤ rmax := hmin.2 hmax.1
  unfold rateOf
  apply div_nonneg <;> linarith

/-- **Corollary 4.5, dynamical form.**  On every unitary Cayley graph `X_n`, `n ≥ 2`, the
optimally tuned iteration satisfies `‖x(t) - x̄ 1‖ ≤ (3/5)^t ‖x(0) - x̄ 1‖`. -/
theorem consensus_three_fifths (hn : 2 ≤ n) :
    ∃ ε > 0, ∀ (x : ZMod n → ℝ) (t : ℕ),
      sqNorm (err ((step ε)^[t] x)) ≤ (((3 : ℝ) / 5) ^ 2) ^ t * sqNorm (err x) := by
  obtain ⟨ρ, hρ⟩ := exists_isRate hn
  obtain ⟨ε, hε, hbound⟩ := consensus_of_isRate hρ
  refine ⟨ε, hε, fun x t => (hbound x t).trans ?_⟩
  have h0 := isRate_nonneg hρ
  have h1 := (rate_le_and_eq_iff hn hρ).1
  refine mul_le_mul_of_nonneg_right ?_ (sqNorm_nonneg _)
  exact pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ h0 h1 2) t

/-- **Corollary 4.5, iteration count.**  `(3/5)^t ≤ δ` as soon as `t ≥ log(1/δ)/log(5/3)`. -/
theorem three_fifths_pow_le {δ : ℝ} (hδ : 0 < δ) {t : ℕ}
    (ht : Real.log (1 / δ) / Real.log (5 / 3) ≤ t) : ((3 : ℝ) / 5) ^ t ≤ δ := by
  have hl : 0 < Real.log (5 / 3) := Real.log_pos (by norm_num)
  have h1 : Real.log (1 / δ) ≤ t * Real.log (5 / 3) := by
    rw [div_le_iff₀ hl] at ht
    exact ht
  have h2 : Real.log (((3 : ℝ) / 5) ^ t) = -(t * Real.log (5 / 3)) := by
    rw [Real.log_pow]
    have : Real.log ((3 : ℝ) / 5) = -Real.log (5 / 3) := by
      rw [← Real.log_inv]
      norm_num
    rw [this]
    ring
  have h3 : Real.log (((3 : ℝ) / 5) ^ t) ≤ Real.log δ := by
    rw [h2]
    have : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    linarith
  exact (Real.log_le_log_iff (by positivity) hδ).mp h3

/-- **Corollary 4.5, numerical instance.**  `28` iterations reduce the error by `10⁶`. -/
theorem twentyeight_iterations : ((3 : ℝ) / 5) ^ 28 ≤ 1 / 10 ^ 6 := by
  norm_num

/-! ### The optimal step (4.6) -/

/-- **Theorem 4.3, the optimal step when `ω(n) ≥ 2`.** -/
theorem opt_step_two_primes {φ p q : ℝ} (hφ : 0 < φ) (hp : 2 ≤ p) (hq : 3 ≤ q) :
    2 / (φ * (1 - 1 / ((p - 1) * (q - 1))) + φ * (p / (p - 1)))
      = 2 * (p - 1) * (q - 1) / (φ * (2 * (p - 1) * (q - 1) + q - 2)) := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : q - 1 ≠ 0 := by linarith
  have hD : 0 < 2 * (p - 1) * (q - 1) + q - 2 := rate_denominator_pos hp hq
  have hS : φ * (1 - 1 / ((p - 1) * (q - 1))) + φ * (p / (p - 1))
      = φ * (2 * (p - 1) * (q - 1) + q - 2) / ((p - 1) * (q - 1)) := by
    field_simp
    ring
  rw [hS]
  field_simp

/-- **Theorem 4.3, the optimal step for `n = p^a`, `a ≥ 2`.** -/
theorem opt_step_prime_pow {φ p : ℝ} (hφ : 0 < φ) (hp : 2 ≤ p) :
    2 / (φ + φ * (p / (p - 1))) = 2 * (p - 1) / ((2 * p - 1) * φ) := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : 2 * p - 1 ≠ 0 := by linarith
  have hS : φ + φ * (p / (p - 1)) = (2 * p - 1) * φ / (p - 1) := by
    field_simp
    ring
  rw [hS]
  field_simp

/-- **Theorem 4.3, the optimal step for `n` prime.** -/
theorem opt_step_prime {m : ℝ} (hm : 0 < m) : 2 / (m + m) = 1 / m := by
  field_simp
  ring

/-! ### Proposition 4.7: the natural step `ε = 1/φ(n)` -/

/-- **Proposition 4.7, contraction factor.**  The non-trivial eigenvalues `r(ord k)` of
`I - L/φ(n) = A/φ(n)` have largest modulus exactly `1/(p-1)`. -/
theorem natural_step_factor (hn : 1 < n) :
    IsGreatest {y : ℝ | ∃ k : ZMod n, k ≠ 0 ∧ |r (addOrderOf k)| = y}
      (1 / ((n.minFac : ℝ) - 1)) := by
  have hn1 : n ≠ 1 := by omega
  have hp := Nat.minFac_prime hn1
  have hp1 : (0 : ℝ) < (n.minFac : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  refine ⟨⟨((n / n.minFac : ℕ) : ZMod n), natCast_div_ne_zero (Nat.minFac_dvd n) hp.one_lt, ?_⟩, ?_⟩
  · rw [addOrderOf_natCast_div (Nat.minFac_dvd n), r_minFac hn1, abs_div, abs_neg, abs_one,
      abs_of_pos hp1]
  · rintro y ⟨k, hk, rfl⟩
    exact abs_r_le_of_dvd (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)

omit [NeZero n] in
/-- **Proposition 4.7, convergence criterion.**  The factor `1/(p-1)` is `< 1` iff `n` is odd. -/
theorem natural_step_lt_one_iff (hn : 1 < n) :
    1 / ((n.minFac : ℝ) - 1) < 1 ↔ Odd n := by
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have hp1 : (0 : ℝ) < (n.minFac : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  rw [div_lt_one hp1, ← Nat.not_even_iff_odd, even_iff_two_dvd, ← Nat.minFac_eq_two_iff]
  constructor
  · intro h h2
    rw [h2] at h
    norm_num at h
  · intro h
    have h3 : 3 ≤ n.minFac := by
      have := hp.two_le
      omega
    have : (3 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast h3
    linarith

/-- The alternating vector `v_j = (-1)^j` on `ℤ/n` for even `n`. -/
noncomputable def alternating (n : ℕ) : ZMod n → ℝ := fun j => (-1) ^ j.val

theorem alternating_add (h2 : 2 ∣ n) (i j : ZMod n) :
    alternating n (i + j) = alternating n i * alternating n j := by
  have key : ∀ m : ℕ, ((-1 : ℝ)) ^ (m % n) = (-1) ^ m := by
    intro m
    obtain ⟨c, hc⟩ := h2
    have e := Nat.mod_add_div m n
    have hev : Even n := ⟨c, by omega⟩
    calc ((-1 : ℝ)) ^ (m % n) = (-1) ^ (m % n) * ((-1) ^ n) ^ (m / n) := by
          rw [Even.neg_one_pow hev, one_pow, mul_one]
      _ = (-1) ^ m := by rw [← pow_mul, ← pow_add, e]
  unfold alternating
  rw [ZMod.val_add, key, pow_add]

omit [NeZero n] in
theorem alternating_unit (h2 : 2 ∣ n) (u : (ZMod n)ˣ) : alternating n u = -1 := by
  unfold alternating
  have hodd : ¬ 2 ∣ (u : ZMod n).val := by
    intro h
    have hc := ZMod.val_coe_unit_coprime u
    have := Nat.dvd_gcd h h2
    rw [hc] at this
    omega
  rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]

/-- **Proposition 4.7, non-convergence for even `n`.**  The alternating vector is a non-zero
sum-zero vector that the natural step maps to its negative, so its error never decays. -/
theorem natural_step_even (h2 : 2 ∣ n) :
    ∑ j, alternating n j = 0 ∧ alternating n ≠ 0 ∧
      step (1 / (Nat.totient n : ℝ)) (alternating n) = fun j => -alternating n j := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  have hn2 : 1 < n := by
    obtain ⟨c, hc⟩ := h2
    have := NeZero.ne n
    omega
  have h1 : ∀ i : ZMod n, alternating n (i + 1) = -alternating n i := by
    intro i
    have hu : IsUnit (1 : ZMod n) := isUnit_one
    rw [alternating_add h2]
    have := alternating_unit h2 hu.unit
    rw [IsUnit.unit_spec] at this
    rw [this]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have := Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (alternating n)
    simp only [Equiv.coe_addRight, h1, sum_neg_distrib] at this
    linarith
  · intro h
    have := congrFun h 0
    simp [alternating] at this
  · funext j
    unfold step lapR
    have : ∀ u : (ZMod n)ˣ, alternating n (j + u) = -alternating n j := by
      intro u
      rw [alternating_add h2, alternating_unit h2]
      ring
    rw [sum_congr rfl fun u _ => this u, sum_const, card_univ, ZMod.card_units_eq_totient,
      nsmul_eq_mul]
    field_simp
    ring

/-! ### Remark 4.8: continuous time -/

/-- **Remark 4.8.**  For a solution of `ẋ = -L x` on `X_n` and any `a` with `a ≤ λ(k)` for all
`k ≠ 0`, `‖x(t) - x̄ 1‖² ≤ e^{-2at} ‖x(0) - x̄ 1‖²` for `t ≥ 0`. -/
theorem continuous_consensus {a : ℝ} (ha : ∀ k : ZMod n, k ≠ 0 → a ≤ lapEig n k)
    (x : ℝ → ZMod n → ℝ) (hx : ∀ t, HasDerivAt x (fun j => -lapR (x t) j) t) {t : ℝ}
    (ht : 0 ≤ t) :
    sqNorm (err (x t)) ≤ Real.exp (-2 * a * t) * sqNorm (err (x 0)) := by
  have hcomp : ∀ s (j : ZMod n), HasDerivAt (fun s => x s j) (-lapR (x s) j) s :=
    fun s j => (hasDerivAt_pi.mp (hx s)) j
  -- the sum, hence the average, is conserved
  have hsum : ∀ s, HasDerivAt (fun s => ∑ j, x s j) 0 s := by
    intro s
    have := HasDerivAt.fun_sum (u := univ) fun j _ => hcomp s j
    simpa [sum_neg_distrib, sum_lapR] using this
  have hconst : ∀ s, avg (x s) = avg (x 0) := by
    intro s
    have hd : Differentiable ℝ (fun s => ∑ j, x s j) := fun s => (hsum s).differentiableAt
    have := is_const_of_deriv_eq_zero hd (fun s => (hsum s).deriv) s 0
    unfold avg
    rw [this]
  set c := avg (x 0) with hc
  set g : ℝ → ℝ := fun s => ∑ j, (x s j - c) ^ 2 with hg
  have hgerr : ∀ s, g s = sqNorm (err (x s)) := by
    intro s
    unfold sqNorm err
    rw [hconst s]
  have hgd : ∀ s, HasDerivAt g (-2 * ∑ j, lapR (fun j => x s j - c) j * (x s j - c)) s := by
    intro s
    have := HasDerivAt.fun_sum (u := univ) fun j _ => ((hcomp s j).sub_const c).pow 2
    convert this using 1
    rw [mul_sum, lapR_sub_const]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hupper : ∀ k : ZMod n, k ≠ 0 → lapEig n k ≤ ∑ k', |lapEig n k'| := fun k _ =>
    (le_abs_self _).trans (single_le_sum (f := fun k' => |lapEig n k'|)
      (fun _ _ => abs_nonneg _) (mem_univ k))
  have hq : ∀ s, a * g s ≤ ∑ j, lapR (fun j => x s j - c) j * (x s j - c) := by
    intro s
    have hz : ∑ j, (x s j - c) = 0 := by
      have := sum_err (x s)
      unfold err at this
      rw [hconst s] at this
      exact this
    exact (quadForm_bounds (fun j => x s j - c) hz ha hupper).1
  set h : ℝ → ℝ := fun s => g s * Real.exp (2 * a * s) with hh
  have hhd : ∀ s, HasDerivAt h ((-2 * ∑ j, lapR (fun j => x s j - c) j * (x s j - c))
      * Real.exp (2 * a * s) + g s * (Real.exp (2 * a * s) * (2 * a))) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (2 * a * s)) (Real.exp (2 * a * s) * (2 * a)) s := by
      have := ((hasDerivAt_id s).const_mul (2 * a)).exp
      simpa using this
    exact (hgd s).mul he
  have hanti : Antitone h := by
    refine antitone_of_hasDerivAt_nonpos hhd fun s => ?_
    have hpos := Real.exp_pos (2 * a * s)
    have hle := mul_le_mul_of_nonneg_left (hq s) hpos.le
    have e : (-2 * ∑ j, lapR (fun j => x s j - c) j * (x s j - c)) * Real.exp (2 * a * s)
        + g s * (Real.exp (2 * a * s) * (2 * a))
        = 2 * (Real.exp (2 * a * s) * (a * g s)
          - Real.exp (2 * a * s) * ∑ j, lapR (fun j => x s j - c) j * (x s j - c)) := by ring
    rw [e]
    simp only [Pi.zero_apply]
    linarith
  have h0 := hanti ht
  simp only [hh, mul_zero, Real.exp_zero, mul_one] at h0
  rw [← hgerr t, ← hgerr 0]
  have hexp : Real.exp (-2 * a * t) * Real.exp (2 * a * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc g t = g t * Real.exp (2 * a * t) * Real.exp (-2 * a * t) := by
          rw [mul_assoc, mul_comm (Real.exp (2 * a * t)), hexp, mul_one]
    _ ≤ g 0 * Real.exp (-2 * a * t) :=
        mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le
    _ = Real.exp (-2 * a * t) * g 0 := by ring

end ArithmeticDynamics
