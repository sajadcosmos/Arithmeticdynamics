/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part IV: the function `r(M) = μ(M)/φ(M)`, its extremal values on the divisors of `n`
(Lemma 3.1 of the paper) and the sign of the instability exponent `g` (Lemma 5.3).
-/
import Mathlib
import ArithmeticDynamics.Arithmetic

namespace ArithmeticDynamics

open ArithmeticFunction

/-- `r M = μ(M) / φ(M)`; the adjacency eigenvalues of `X_n` are `φ(n) · r(M)`. -/
noncomputable def r (M : ℕ) : ℝ := (moebius M : ℝ) / (Nat.totient M : ℝ)

theorem r_one : r 1 = 1 := by simp [r]

theorem r_prime {p : ℕ} (hp : p.Prime) : r p = -1 / ((p : ℝ) - 1) := by
  simp [r, moebius_apply_prime hp, Nat.totient_prime hp, Nat.cast_sub hp.one_le]

theorem abs_r_le (M : ℕ) : |r M| ≤ 1 / (Nat.totient M : ℝ) := by
  have h : |(moebius M : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := M))
  rw [r, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (Nat.totient M : ℝ) from Nat.cast_nonneg _)]
  gcongr

theorem abs_r_le_half {M : ℕ} (hM : 3 ≤ M) : |r M| ≤ 1 / 2 := by
  have hev : Even (Nat.totient M) := Nat.totient_even (by omega)
  have hpos : 0 < Nat.totient M := Nat.totient_pos.mpr (by omega)
  have h2 : 2 ≤ Nat.totient M := by
    obtain ⟨k, hk⟩ := hev
    omega
  have h2' : (2 : ℝ) ≤ (Nat.totient M : ℝ) := by exact_mod_cast h2
  calc |r M| ≤ 1 / (Nat.totient M : ℝ) := abs_r_le M
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2'

/-- **Lemma 3.1 (i).**  For every divisor `M > 1` of `n`, `r M ≥ -1/(p-1)` with `p = minFac n`. -/
theorem r_ge_of_dvd {n M : ℕ} (hM : 1 < M) (hMn : M ∣ n) :
    -1 / ((n.minFac : ℝ) - 1) ≤ r M := by
  have hn1 : n ≠ 1 := by
    rintro rfl
    have := Nat.le_of_dvd Nat.one_pos hMn
    omega
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hle : n.minFac - 1 ≤ Nat.totient M := minFac_pred_le_totient hM hMn
  have hle' : (n.minFac : ℝ) - 1 ≤ (Nat.totient M : ℝ) := by
    have : ((n.minFac - 1 : ℕ) : ℝ) ≤ (Nat.totient M : ℝ) := by exact_mod_cast hle
    rwa [Nat.cast_sub hp.one_le, Nat.cast_one] at this
  have hpos : (0 : ℝ) < (n.minFac : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have h1 := abs_r_le M
  have h2 : 1 / (Nat.totient M : ℝ) ≤ 1 / ((n.minFac : ℝ) - 1) :=
    one_div_le_one_div_of_le hpos hle'
  have h3 := neg_abs_le (r M)
  rw [neg_div]
  linarith

/-- **Lemma 3.1 (i), attainment.**  `r(p) = -1/(p-1)` at `p = minFac n`. -/
theorem r_minFac {n : ℕ} (hn : n ≠ 1) : r n.minFac = -1 / ((n.minFac : ℝ) - 1) :=
  r_prime (Nat.minFac_prime hn)

/-- For distinct primes `p`, `q`: `r(pq) = 1/((p-1)(q-1))`. -/
theorem r_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    r (p * q) = 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hμ : moebius (p * q) = 1 := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp,
      moebius_apply_prime hq]
    norm_num
  rw [r, hμ, Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]
  push_cast [Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le]
  ring

/-- If `μ(M) = 1` and `M > 1`, then `M` is divisible by two distinct primes. -/
theorem exists_two_primes_of_moebius_eq_one {M : ℕ} (hM : 1 < M) (h : moebius M = 1) :
    ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a ≠ b ∧ a * b ∣ M := by
  have hsq : Squarefree M := moebius_ne_zero_iff_squarefree.mp (by rw [h]; norm_num)
  have hnp : ¬ M.Prime := by
    intro hpr
    rw [moebius_apply_prime hpr] at h
    norm_num at h
  have ha : M.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd M
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hnp (hm ▸ ha)
  have hb : m.minFac.Prime := Nat.minFac_prime hm1
  refine ⟨M.minFac, m.minFac, ha, hb, ?_, ?_⟩
  · intro heq
    have hdvd : M.minFac * M.minFac ∣ M := by
      conv_rhs => rw [hm]
      exact Nat.mul_dvd_mul_left _ (heq ▸ Nat.minFac_dvd m)
    have := Nat.isUnit_iff.mp (hsq _ hdvd)
    exact ha.one_lt.ne' this
  · conv_rhs => rw [hm]
    exact Nat.mul_dvd_mul_left _ (Nat.minFac_dvd m)

/-- **Lemma 3.1 (ii).**  Let `p < q` be the two smallest prime divisors of `n`, encoded by
the hypothesis that every prime divisor of `n` is `p` or at least `q`.  Then for every
divisor `M > 1` of `n`, `r M ≤ 1/((p-1)(q-1))`. -/
theorem r_le_of_dvd {n p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hprimes : ∀ l : ℕ, l.Prime → l ∣ n → l = p ∨ q ≤ l) (hM : 1 < M) (hMn : M ∣ n) :
    r M ≤ 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    linarith
  have hrhs : (0 : ℝ) < 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by positivity
  have hφ : (0 : ℝ) ≤ (Nat.totient M : ℝ) := Nat.cast_nonneg _
  rcases moebius_eq_or M with h | h | h
  · have : r M = 0 := by simp [r, h]
    linarith
  · obtain ⟨a, b, ha, hb, hab, hdvd⟩ := exists_two_primes_of_moebius_eq_one hM h
    have hcop : Nat.Coprime a b := (Nat.coprime_primes ha hb).mpr hab
    have han : a ∣ n := dvd_trans (dvd_trans (Dvd.intro _ rfl) hdvd) hMn
    have hbn : b ∣ n := dvd_trans (dvd_trans (Dvd.intro_left _ rfl) hdvd) hMn
    have hMpos : 0 < M := by omega
    have h1 : (a - 1) * (b - 1) ≤ Nat.totient M := by
      have hd := Nat.totient_dvd_of_dvd hdvd
      rw [Nat.totient_mul hcop, Nat.totient_prime ha, Nat.totient_prime hb] at hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hMpos) hd
    have h2 : (p - 1) * (q - 1) ≤ (a - 1) * (b - 1) := by
      rcases hprimes a ha han with ha' | ha' <;> rcases hprimes b hb hbn with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · subst ha'
        exact Nat.mul_le_mul_left _ (by omega)
      · subst hb'
        rw [Nat.mul_comm (b - 1) (q - 1)]
        exact Nat.mul_le_mul_right _ (by omega)
      · exact Nat.mul_le_mul (by omega) (by omega)
    have h3 : ((p : ℝ) - 1) * ((q : ℝ) - 1) ≤ (Nat.totient M : ℝ) := by
      have : (((p - 1) * (q - 1) : ℕ) : ℝ) ≤ (Nat.totient M : ℝ) := by
        exact_mod_cast h2.trans h1
      rwa [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_one] at this
    have : r M = 1 / (Nat.totient M : ℝ) := by simp [r, h]
    rw [this]
    exact one_div_le_one_div_of_le (mul_pos hp1 hq1) h3
  · have : r M = -1 / (Nat.totient M : ℝ) := by simp [r, h]
    have h0 : (1 : ℝ) / (Nat.totient M : ℝ) ≥ 0 := by positivity
    rw [this, neg_div]
    linarith

/-- **Lemma 3.1 (iii).**  If `n = p^a`, every divisor `M > 1` has `r M ≤ 0`. -/
theorem r_le_zero_of_dvd_prime_pow {p a M : ℕ} (hp : p.Prime) (hM : 1 < M) (h : M ∣ p ^ a) :
    r M ≤ 0 := by
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp h
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hM
  rw [r, moebius_apply_prime_pow hp hk]
  have h0 : (1 : ℝ) / (Nat.totient (p ^ k) : ℝ) ≥ 0 := by positivity
  split_ifs
  · push_cast
    rw [neg_div]
    linarith
  · simp

/-- **Lemma 3.1 (iii), attainment.**  `r(p²) = 0`. -/
theorem r_prime_sq {p : ℕ} (hp : p.Prime) : r (p ^ 2) = 0 := by
  rw [r, moebius_apply_prime_pow hp (by norm_num)]
  simp

/-! ### The instability exponent -/

/-- `g M = (1 + r(M / gcd(2, M)))/2 - r M`; the Jacobian at a twisted state of order `M`
has the eigenvalue `K · g M` (Section 5.1 of the paper). -/
noncomputable def g (M : ℕ) : ℝ := (1 + r (M / Nat.gcd 2 M)) / 2 - r M

theorem r_two : r 2 = -1 := by
  rw [r_prime Nat.prime_two]
  norm_num

theorem r_three : r 3 = -1 / 2 := by
  rw [r_prime Nat.prime_three]
  norm_num

theorem r_six : r 6 = 1 / 2 := by
  have h := r_mul_primes Nat.prime_two Nat.prime_three (by norm_num)
  norm_num at h
  exact h

theorem r_eq_zero_of_four_dvd {M : ℕ} (h : 4 ∣ M) : r M = 0 := by
  have hns : ¬ Squarefree M := by
    intro hsq
    have h22 : 2 * 2 ∣ M := by simpa using h
    have := Nat.isUnit_iff.mp (hsq 2 h22)
    norm_num at this
  simp [r, moebius_eq_zero_of_not_squarefree hns]

/-- **Lemma 5.3.**  `g(2) = 2`. -/
theorem g_two : g 2 = 2 := by
  have h : 2 / Nat.gcd 2 2 = 1 := by norm_num
  rw [g, h, r_one, r_two]
  norm_num

/-- **Lemma 5.3.**  `g(4) = 0`. -/
theorem g_four : g 4 = 0 := by
  have h : 4 / Nat.gcd 2 4 = 2 := by norm_num
  rw [g, h, r_two, r_eq_zero_of_four_dvd (dvd_refl 4)]
  norm_num

/-- **Lemma 5.3.**  `g(6) = -1/4`. -/
theorem g_six : g 6 = -1 / 4 := by
  have h : 6 / Nat.gcd 2 6 = 3 := by norm_num
  rw [g, h, r_three, r_six]
  norm_num

/-- An odd number `M ≥ 5` has `φ(M) ≥ 4`. -/
theorem four_le_totient_of_odd {M : ℕ} (hodd : Odd M) (hM : 5 ≤ M) : 4 ≤ Nat.totient M := by
  have hev : Even (Nat.totient M) := Nat.totient_even (by omega)
  have hpos : 0 < Nat.totient M := Nat.totient_pos.mpr (by omega)
  by_contra hlt
  have h2 : Nat.totient M = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  -- every prime divisor `l` of `M` has `l - 1 ≤ 2`, and `l` is odd, hence `l = 3`
  have hl : ∀ l : ℕ, l.Prime → l ∣ M → l = 3 := by
    intro l hlp hlM
    have h1 := pred_prime_le_totient hlp hlM (by omega)
    have hl2 : l ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨c, hc⟩ := hlM
      omega
    have := hlp.two_le
    omega
  have h3 : M.minFac = 3 := hl _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd M)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd M
  rw [h3] at hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    omega
  have hm3 : m.minFac = 3 :=
    hl _ (Nat.minFac_prime hm1) (dvd_trans (Nat.minFac_dvd m) (Dvd.intro_left 3 hm.symm))
  obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
  rw [hm3] at hm'
  have h9 : 9 ∣ M := ⟨m', by rw [hm, hm']; ring⟩
  have h6 : Nat.totient 9 ∣ Nat.totient M := Nat.totient_dvd_of_dvd h9
  have ht9 : Nat.totient 9 = 6 := by decide
  rw [ht9, h2] at h6
  omega

theorem abs_r_le_quarter {M : ℕ} (hodd : Odd M) (hM : 5 ≤ M) : |r M| ≤ 1 / 4 := by
  have h4 : (4 : ℝ) ≤ (Nat.totient M : ℝ) := by exact_mod_cast four_le_totient_of_odd hodd hM
  calc |r M| ≤ 1 / (Nat.totient M : ℝ) := abs_r_le M
    _ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4

theorem r_two_mul_of_odd {M : ℕ} (hodd : Odd M) : r (2 * M) = - r M := by
  have hcop : Nat.Coprime 2 M := Nat.coprime_two_left.mpr hodd
  rw [r, r, isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime Nat.prime_two,
    Nat.totient_two_mul_of_odd hodd]
  push_cast
  ring

/-- **Lemma 5.3.**  `g M ≥ 1/8` for every `M ≥ 2` other than `4` and `6`. -/
theorem g_ge {M : ℕ} (hM : 2 ≤ M) (h4 : M ≠ 4) (h6 : M ≠ 6) : 1 / 8 ≤ g M := by
  rcases Nat.even_or_odd M with he | ho
  · obtain ⟨N, hN⟩ := he
    have hN2 : M = 2 * N := by omega
    subst hN2
    have hgcd : 2 * N / Nat.gcd 2 (2 * N) = N := by
      have h2 : Nat.gcd 2 (2 * N) = 2 := Nat.gcd_eq_left (Dvd.intro N rfl)
      rw [h2]
      exact Nat.mul_div_cancel_left N (by norm_num)
    rcases Nat.even_or_odd N with he' | ho'
    · -- 4 ∣ M
      have h4dvd : 4 ∣ 2 * N := by
        obtain ⟨k, hk⟩ := he'
        exact ⟨k, by omega⟩
      have hN3 : 3 ≤ N := by
        obtain ⟨k, hk⟩ := he'
        omega
      have := abs_le.mp (abs_r_le_half hN3)
      rw [g, hgcd, r_eq_zero_of_four_dvd h4dvd]
      linarith [this.1]
    · rw [g, hgcd, r_two_mul_of_odd ho']
      by_cases hN1 : N = 1
      · subst hN1
        rw [r_one]
        norm_num
      · have hN5 : 5 ≤ N := by
          obtain ⟨k, hk⟩ := ho'
          omega
        have := abs_le.mp (abs_r_le_quarter ho' hN5)
        linarith [this.1]
  · have hcop : Nat.gcd 2 M = 1 := Nat.coprime_two_left.mpr ho
    have hM3 : 3 ≤ M := by
      obtain ⟨k, hk⟩ := ho
      omega
    have := abs_le.mp (abs_r_le_half hM3)
    rw [g, hcop, Nat.div_one]
    linarith [this.2]

end ArithmeticDynamics
