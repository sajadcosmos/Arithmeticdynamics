/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XIX: the mathematical content of the remarks — the set of values of `ρ*` (Remark 4.4),
the phase lags at hexagonal states (Remarks 5.8 and 6.4), the density bound (Remark 5.9),
and the quarter twists on gcd graphs (Remark 6.4).
-/
import Mathlib
import ArithmeticDynamics.GcdGraph

namespace ArithmeticDynamics

open Finset Real Filter Topology ArithmeticFunction

/-! ### Remark 4.4: the set of values of the optimal rate -/

/-- For fixed `p`, the rate `q/(2(p-1)(q-1)+q-2)` is strictly decreasing in `q`. -/
theorem rate_strictAnti_q {p q₁ q₂ : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q₁) (hlt : q₁ < q₂) :
    q₂ / (2 * (p - 1) * (q₂ - 1) + q₂ - 2) < q₁ / (2 * (p - 1) * (q₁ - 1) + q₁ - 2) := by
  have h1 := rate_denominator_pos hp hq
  have h2 := rate_denominator_pos hp (show 3 ≤ q₂ by linarith)
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith

/-- For fixed `p`, the rate tends to `1/(2p-1)` as `q → ∞`, the value at the prime powers of `p`. -/
theorem rate_tendsto_q {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun q : ℝ => q / (2 * (p - 1) * (q - 1) + q - 2)) atTop (𝓝 (1 / (2 * p - 1))) := by
  have hA : 0 < 2 * p - 1 := by linarith
  have h : Tendsto (fun q : ℝ => 1 / ((2 * p - 1) - 2 * p / q)) atTop (𝓝 (1 / (2 * p - 1))) := by
    have h0 : Tendsto (fun q : ℝ => 2 * p / q) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := (tendsto_const_nhds (x := 2 * p - 1)).sub h0
    rw [sub_zero] at this
    exact (tendsto_const_nhds.div this hA.ne')
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with q hq
  have hq0 : q ≠ 0 := by linarith
  have hD := rate_denominator_pos hp hq
  have e : (2 * p - 1) - 2 * p / q = (2 * (p - 1) * (q - 1) + q - 2) / q := by
    field_simp
    ring
  rw [e, one_div_div]

/-- The prime-power values `1/(2p-1)` accumulate at `0`. -/
theorem rate_prime_pow_tendsto : Tendsto (fun p : ℝ => 1 / (2 * p - 1)) atTop (𝓝 0) := by
  have : Tendsto (fun p : ℝ => 2 * p - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by norm_num))
  refine this.inv_tendsto_atTop.congr fun p => ?_
  simp [one_div]

/-- **Remark 4.4, even moduli.**  For even `n > 2`, `1/3 ≤ ρ*(X_n) ≤ 3/5`. -/
theorem rate_even {m : ℕ} (hm : 2 < m) (heven : 2 ∣ m) {ρ : ℝ} (h : IsRate m ρ) :
    1 / 3 ≤ ρ ∧ ρ ≤ 3 / 5 := by
  refine ⟨?_, (rate_le_and_eq_iff hm.le h).1⟩
  have hmin : m.minFac = 2 := (Nat.minFac_eq_two_iff m).mpr heven
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow heven)).symm
    subst hp2
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have : k = 1 := by omega
      subst this
      omega
    rw [h.unique (isRate_prime_pow Nat.prime_two hk2)]
    norm_num
  · obtain ⟨q, hts⟩ := exists_twoSmallest hm.le hpp
    rw [h.unique (isRate_of_twoSmallest hm.le hts), hmin]
    have hq3 : (3 : ℝ) ≤ q := by
      have : 3 ≤ q := by have := hts.hlt; rw [hmin] at this; omega
      exact_mod_cast this
    have hD : (0 : ℝ) < 2 * (((2 : ℕ) : ℝ) - 1) * (q - 1) + q - 2 := by push_cast; linarith
    rw [le_div_iff₀ hD]
    push_cast
    linarith

/-- **Remark 4.4, odd moduli.**  For odd `n ≥ 3`, `ρ*(X_n) ≤ 5/19`, with equality iff `15 ∣ n`. -/
theorem rate_odd {m : ℕ} (hm : 2 ≤ m) (hodd : ¬ 2 ∣ m) {ρ : ℝ} (h : IsRate m ρ) :
    ρ ≤ 5 / 19 ∧ (ρ = 5 / 19 ↔ 15 ∣ m) := by
  have hmin3 : 3 ≤ m.minFac := by
    have hp := Nat.minFac_prime (show m ≠ 1 by omega)
    have h2 : m.minFac ≠ 2 := fun h2 => hodd (h2 ▸ Nat.minFac_dvd m)
    have := hp.two_le
    omega
  have h15 : ¬ 15 ∣ m → True := fun _ => trivial
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
    have hminp : (p ^ k).minFac = p := Nat.Prime.pow_minFac hp (by omega)
    rw [hminp] at hmin3
    have hn15 : ¬ 15 ∣ p ^ k := by
      intro h15
      have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
      have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).mp
        ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
      omega
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      subst this
      rw [pow_one] at h hn15 ⊢
      rw [h.unique (isRate_prime hp)]
      exact ⟨by norm_num, by constructor <;> intro h' <;> [norm_num at h'; exact absurd h' hn15]⟩
    · rw [h.unique (isRate_prime_pow hp hk2)]
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hmin3
      have hlt : 1 / (2 * (p : ℝ) - 1) < 5 / 19 := by
        rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
        linarith
      exact ⟨hlt.le, by constructor <;> intro h' <;> [linarith; exact absurd h' hn15]⟩
  · obtain ⟨q, hts⟩ := exists_twoSmallest hm hpp
    rw [h.unique (isRate_of_twoSmallest hm hts)]
    set p := m.minFac with hpdef
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hmin3
    have hq5n : 5 ≤ q := by
      have hlt := hts.hlt
      have hq := hts.hq
      by_contra hq5
      have : q = 4 := by
        have := hq.two_le
        omega
      subst this
      exact absurd hq (by norm_num)
    have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast hq5n
    have hD : (0 : ℝ) < 2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2 := by nlinarith
    have h0 : 0 ≤ ((p : ℝ) - 3) * ((q : ℝ) - 5) := mul_nonneg (by linarith) (by linarith)
    refine ⟨?_, ?_⟩
    · rw [div_le_div_iff₀ hD (by norm_num)]
      nlinarith
    · constructor
      · intro heq
        rw [div_eq_div_iff hD.ne' (by norm_num)] at heq
        have hp' : (p : ℝ) = 3 := by nlinarith
        have hq' : (q : ℝ) = 5 := by nlinarith
        have hpn : p = 3 := by exact_mod_cast hp'
        have hqn : q = 5 := by exact_mod_cast hq'
        have h3 : 3 ∣ m := by
          have e : m.minFac = 3 := hpn
          rw [← e]; exact Nat.minFac_dvd m
        have h5 : 5 ∣ m := by have := hts.hqn; rwa [hqn] at this
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
      · intro h15
        have h3 : 3 ∣ m := dvd_trans (by norm_num) h15
        have h5 : 5 ∣ m := dvd_trans (by norm_num) h15
        have hpn : p = 3 := le_antisymm (hts.least 3 Nat.prime_three h3) hmin3
        have hqn : q = 5 :=
          le_antisymm (hts.second 5 (by norm_num) h5 (by omega)) hq5n
        rw [hpn, hqn]
        norm_num

/-! ### Remark 5.9: the density of `X_n` for `6 ∣ n` -/

/-- **Remark 5.9.**  If `6 ∣ n`, then `3 φ(n) ≤ n`, with equality iff the only prime divisors of
`n` are `2` and `3`. -/
theorem totient_le_third {m : ℕ} (hm0 : m ≠ 0) (h6 : 6 ∣ m) :
    3 * Nat.totient m ≤ m ∧ (3 * Nat.totient m = m ↔ m.primeFactors = {2, 3}) := by
  set P := m.primeFactors
  have h2P : 2 ∈ P := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num) h6, hm0⟩
  have h3P : 3 ∈ P := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_trans (by norm_num) h6, hm0⟩
  set R := (P.erase 2).erase 3
  have hPR : P = insert 2 (insert 3 R) := by
    rw [insert_erase (mem_erase.mpr ⟨by norm_num, h3P⟩), insert_erase h2P]
  have h2R : 2 ∉ insert 3 R := by simp [R]
  have h3R : 3 ∉ R := by simp [R]
  have key : Nat.totient m * ∏ p ∈ P, p = m * ∏ p ∈ P, (p - 1) :=
    Nat.totient_mul_prod_primeFactors m
  rw [hPR, prod_insert h2R, prod_insert h3R, prod_insert h2R, prod_insert h3R] at key
  have hRpos : 0 < ∏ p ∈ R, p := prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hp))).pos
  have hle : ∏ p ∈ R, (p - 1) ≤ ∏ p ∈ R, p := prod_le_prod' fun p _ => Nat.sub_le p 1
  -- key : φ m * (2 * (3 * ∏ R p)) = m * ((2 - 1) * ((3 - 1) * ∏ R (p - 1)))
  norm_num at key
  have hmain : 3 * Nat.totient m * ∏ p ∈ R, p = m * ∏ p ∈ R, (p - 1) := by linarith
  constructor
  · have : 3 * Nat.totient m * ∏ p ∈ R, p ≤ m * ∏ p ∈ R, p := by
      rw [hmain]; exact Nat.mul_le_mul_left m hle
    exact Nat.le_of_mul_le_mul_right this hRpos
  · constructor
    · intro heq
      rw [heq] at hmain
      have hRR : ∏ p ∈ R, p = ∏ p ∈ R, (p - 1) :=
        Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) hmain
      have hRe : R = ∅ := by
        by_contra hne
        have hlt : ∏ p ∈ R, (p - 1) < ∏ p ∈ R, p := by
          refine prod_lt_prod_of_nonempty₀ (fun p hp => ?_) (fun p hp => ?_)
            (nonempty_iff_ne_empty.mpr hne)
          · have := (Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hp))).two_le
            omega
          · have := (Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hp))).two_le
            omega
        omega
      rw [hPR, hRe]
      rfl
    · intro hP
      have hRe : R = ∅ := by
        simp only [R, hP]
        decide
      rw [hRe, prod_empty, prod_empty, mul_one, mul_one] at hmain
      exact hmain

/-- **Remark 5.9.**  For `6 ∣ n`, the relative degree of `X_n` is below the `75%` density
threshold: `φ(n)/(n-1) < 3/4`. -/
theorem relative_degree_lt {m : ℕ} (hm0 : m ≠ 0) (h6 : 6 ∣ m) :
    (Nat.totient m : ℝ) / ((m : ℝ) - 1) < 3 / 4 := by
  have hm6 : 6 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h6
  have h := (totient_le_third hm0 h6).1
  have hm : (6 : ℝ) ≤ m := by exact_mod_cast hm6
  have h' : 3 * (Nat.totient m : ℝ) ≤ m := by exact_mod_cast h
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-! ### Remarks 5.8 and 6.4: phase lags at the hexagonal state -/

/-- The phase lag `π s/3` across an edge of step `s` at the hexagonal state has cosine `1`, `1/2`,
`-1/2` or `-1` according to `gcd(s, 6) = 6, 1, 2, 3`. -/
theorem cos_hex_cases (s : ℤ) :
    (6 ∣ s → cos (π * s / 3) = 1) ∧
    (¬ 2 ∣ s → ¬ 3 ∣ s → cos (π * s / 3) = 1 / 2) ∧
    (2 ∣ s → ¬ 3 ∣ s → cos (π * s / 3) = -1 / 2) ∧
    (¬ 2 ∣ s → 3 ∣ s → cos (π * s / 3) = -1) := by
  refine ⟨fun h => ?_, fun h2 h3 => cos_hexagonal s h2 h3, fun h2 h3 => ?_, fun h2 h3 => ?_⟩
  · obtain ⟨k, rfl⟩ := h
    have : π * ((6 * k : ℤ) : ℝ) / 3 = (k : ℝ) * (2 * π) := by push_cast; ring
    rw [this, cos_int_mul_two_pi]
  · have hk : ∃ k : ℤ, s = 6 * k + 2 ∨ s = 6 * k - 2 := by
      have : s % 6 = 2 ∨ s % 6 = 4 := by omega
      rcases this with h | h
      · exact ⟨s / 6, Or.inl (by omega)⟩
      · exact ⟨s / 6 + 1, Or.inr (by omega)⟩
    obtain ⟨k, rfl | rfl⟩ := hk
    · have : π * ((6 * k + 2 : ℤ) : ℝ) / 3 = 2 * π / 3 + (k : ℝ) * (2 * π) := by push_cast; ring
      rw [this, cos_add_int_mul_two_pi]
      have : 2 * π / 3 = π - π / 3 := by ring
      rw [this, cos_pi_sub, cos_pi_div_three]
      ring
    · have : π * ((6 * k - 2 : ℤ) : ℝ) / 3 = -(2 * π / 3) + (k : ℝ) * (2 * π) := by push_cast; ring
      rw [this, cos_add_int_mul_two_pi, cos_neg]
      have : 2 * π / 3 = π - π / 3 := by ring
      rw [this, cos_pi_sub, cos_pi_div_three]
      ring
  · have hk : ∃ k : ℤ, s = 6 * k + 3 := ⟨s / 6, by omega⟩
    obtain ⟨k, rfl⟩ := hk
    have : π * ((6 * k + 3 : ℤ) : ℝ) / 3 = π + (k : ℝ) * (2 * π) := by push_cast; ring
    rw [this, cos_add_int_mul_two_pi, cos_pi]

variable {n : ℕ} [NeZero n]

/-- **Remark 6.4, quarter twists on gcd graphs.**  If `4 ∣ n` and every element of `D` is odd,
every edge weight at the quarter twist `m = n/4` of `X_n(D)` vanishes, hence so does the
Jacobian. -/
theorem cWeight_quarter_gcd (h4 : 4 ∣ n) {D : Finset ℕ} (hDodd : ∀ d ∈ D, Odd d)
    {s : ZMod n} (hs : s ∈ gcdSet n D) : cWeight ((n / 4 : ℕ) : ZMod n) s = 0 := by
  simp only [gcdSet, mem_filter, mem_univ, true_and] at hs
  have hodd : ¬ 2 ∣ s.val := by
    intro h
    have : 2 ∣ Nat.gcd s.val n := Nat.dvd_gcd h (dvd_trans (by norm_num) h4)
    obtain ⟨j, hj⟩ := hDodd _ hs
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (s.val : ℤ) = 2 * k + 1 := ⟨(s.val : ℤ) / 2, by omega⟩
  obtain ⟨t, ht⟩ := h4
  have ht0 : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by rintro rfl; exact NeZero.ne n (by simpa using ht)
    exact_mod_cast this
  have hdiv : n / 4 = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by norm_num)
  unfold cWeight
  rw [natCast_mul_val, stdAddChar_natCast_re, hdiv, ← cos_quarter k]
  congr 1
  have hn : (n : ℝ) = 4 * (t : ℝ) := by exact_mod_cast ht
  have hv : ((s.val : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by exact_mod_cast hk
  rw [hn]
  push_cast
  push_cast at hv
  rw [hv]
  field_simp
  ring

theorem cJac_quarter_gcd (h4 : 4 ∣ n) {D : Finset ℕ} (hDodd : ∀ d ∈ D, Odd d) (K : ℝ)
    (f : ZMod n → ℝ) (i : ZMod n) : cJac (gcdSet n D) K ((n / 4 : ℕ) : ZMod n) f i = 0 := by
  unfold cJac
  rw [sum_eq_zero fun s hs => by rw [cWeight_quarter_gcd h4 hDodd hs, zero_mul], mul_zero]

/-- **Lemma 5.3.**  `g(1) = 0`. -/
theorem g_one : g 1 = 0 := by
  unfold g
  norm_num [r_one]

end ArithmeticDynamics
