/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XI: equality cases of Lemma 3.1, exact multiplicities in Theorem 3.2, and the
spectral ratio of Corollary 3.3.
-/
import Mathlib
import ArithmeticDynamics.Rates

namespace ArithmeticDynamics

open ArithmeticFunction Finset

/-- A squarefree non-prime `M > 1` is divisible by two distinct primes. -/
theorem two_primes_of_not_prime {M : ℕ} (hM : 1 < M) (hsq : Squarefree M) (hnp : ¬ M.Prime) :
    ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a ≠ b ∧ a * b ∣ M := by
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
    exact ha.one_lt.ne' (Nat.isUnit_iff.mp (hsq _ hdvd))
  · conv_rhs => rw [hm]
    exact Nat.mul_dvd_mul_left _ (Nat.minFac_dvd m)

theorem totient_ge_of_two_primes {M a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (hdvd : a * b ∣ M) (hM : 0 < M) : (a - 1) * (b - 1) ≤ Nat.totient M := by
  have hcop : Nat.Coprime a b := (Nat.coprime_primes ha hb).mpr hab
  have hd := Nat.totient_dvd_of_dvd hdvd
  rw [Nat.totient_mul hcop, Nat.totient_prime ha, Nat.totient_prime hb] at hd
  exact Nat.le_of_dvd (Nat.totient_pos.mpr hM) hd

/-- **Lemma 3.1 (i), equality case.**  `r M = -1/(p-1)` for a divisor `M > 1` of `n` iff `M = p`. -/
theorem r_eq_min_iff {n M : ℕ} (hM : 1 < M) (hMn : M ∣ n) :
    r M = -1 / ((n.minFac : ℝ) - 1) ↔ M = n.minFac := by
  have hn1 : n ≠ 1 := by
    rintro rfl
    have := Nat.le_of_dvd Nat.one_pos hMn
    omega
  have hp := Nat.minFac_prime hn1
  constructor
  · intro h
    set p := n.minFac with hpdef
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      linarith
    have hneg : r M < 0 := by
      rw [h, neg_div]
      exact neg_neg_of_pos (by positivity)
    have hμ : moebius M = -1 := by
      rcases moebius_eq_or M with h0 | h0 | h0
      · simp [r, h0] at hneg
      · have : 0 ≤ r M := by simp [r, h0]
        linarith
      · exact h0
    have hφ : Nat.totient M = p - 1 := by
      rw [r, hμ] at h
      have hφpos : (0 : ℝ) < (Nat.totient M : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have e : (Nat.totient M : ℝ) = (p : ℝ) - 1 := by
        field_simp at h
        push_cast at h
        linarith
      have : ((Nat.totient M : ℕ) : ℝ) = ((p - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hp.one_le, Nat.cast_one]
        exact e
      exact_mod_cast this
    have hsq : Squarefree M := moebius_ne_zero_iff_squarefree.mp (by rw [hμ]; norm_num)
    by_cases hpr : M.Prime
    · have : M - 1 = p - 1 := by rw [← Nat.totient_prime hpr, hφ]
      have := hpr.two_le
      have := hp.two_le
      omega
    · exfalso
      obtain ⟨a, b, ha, hb, hab, hdvd⟩ := two_primes_of_not_prime hM hsq hpr
      have hle := totient_ge_of_two_primes ha hb hab hdvd (by omega)
      have han : a ∣ n := dvd_trans (dvd_trans (Dvd.intro _ rfl) hdvd) hMn
      have hbn : b ∣ n := dvd_trans (dvd_trans (Dvd.intro_left _ rfl) hdvd) hMn
      have hpa : p ≤ a := Nat.minFac_le_of_dvd ha.two_le han
      have hpb : p ≤ b := Nat.minFac_le_of_dvd hb.two_le hbn
      have hp2 := hp.two_le
      rw [hφ] at hle
      rcases Nat.lt_or_gt_of_ne hab with h' | h'
      · have h1 : (p - 1) * 2 ≤ (a - 1) * (b - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      · have h1 : 2 * (p - 1) ≤ (a - 1) * (b - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
  · rintro rfl
    exact r_minFac hn1

/-- **Lemma 3.1 (ii), equality case.**  If `p < q` are the two smallest prime divisors of `n`,
then `r M = 1/((p-1)(q-1))` for a divisor `M > 1` of `n` iff `M = p q`. -/
theorem r_eq_max_iff {n p q M : ℕ} (h : TwoSmallest n p q) (hM : 1 < M) (hMn : M ∣ n) :
    r M = 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) ↔ M = p * q := by
  have hne : p ≠ q := by have := h.hlt; omega
  constructor
  · intro hr
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.hp.two_le
      linarith
    have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h.hq.two_le
      linarith
    have hpos : 0 < r M := by rw [hr]; positivity
    have hμ : moebius M = 1 := by
      rcases moebius_eq_or M with h0 | h0 | h0
      · simp [r, h0] at hpos
      · exact h0
      · have : r M ≤ 0 := by
          simp only [r, h0]
          push_cast
          rw [neg_div]
          exact neg_nonpos.mpr (by positivity)
        linarith
    have hφ : Nat.totient M = (p - 1) * (q - 1) := by
      rw [r, hμ] at hr
      have hφpos : (0 : ℝ) < (Nat.totient M : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have e : (Nat.totient M : ℝ) = ((p : ℝ) - 1) * ((q : ℝ) - 1) := by
        field_simp at hr
        push_cast at hr
        linarith
      have : ((Nat.totient M : ℕ) : ℝ) = (((p - 1) * (q - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub h.hp.one_le, Nat.cast_sub h.hq.one_le, Nat.cast_one]
        exact e
      exact_mod_cast this
    have hsq : Squarefree M := moebius_ne_zero_iff_squarefree.mp (by rw [hμ]; norm_num)
    obtain ⟨a, b, ha, hb, hab, hdvd⟩ := exists_two_primes_of_moebius_eq_one hM hμ
    have hle := totient_ge_of_two_primes ha hb hab hdvd (by omega)
    rw [hφ] at hle
    have han : a ∣ n := dvd_trans (dvd_trans (Dvd.intro _ rfl) hdvd) hMn
    have hbn : b ∣ n := dvd_trans (dvd_trans (Dvd.intro_left _ rfl) hdvd) hMn
    have hp2 := h.hp.two_le
    have hlt := h.hlt
    -- the pair `{a, b}` must be `{p, q}`
    have hpq : a * b = p * q := by
      rcases h.primes a ha han with ha' | ha' <;> rcases h.primes b hb hbn with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · subst ha'
        have : (a - 1) * (b - 1) ≤ (a - 1) * (q - 1) := hle
        have h3 : b - 1 ≤ q - 1 := Nat.le_of_mul_le_mul_left this (by omega)
        have : b = q := by omega
        rw [this]
      · subst hb'
        have : (b - 1) * (a - 1) ≤ (b - 1) * (q - 1) := by rw [Nat.mul_comm]; exact hle
        have h3 : a - 1 ≤ q - 1 := Nat.le_of_mul_le_mul_left this (by omega)
        have : a = q := by omega
        rw [this, Nat.mul_comm]
      · exfalso
        rcases Nat.lt_or_gt_of_ne hab with h' | h'
        · have h1 : (q - 1) * q ≤ (a - 1) * (b - 1) := Nat.mul_le_mul (by omega) (by omega)
          have h2 : (p - 1) * (q - 1) < (q - 1) * q := by
            rw [Nat.mul_comm]
            exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
          omega
        · have h1 : q * (q - 1) ≤ (a - 1) * (b - 1) := Nat.mul_le_mul (by omega) (by omega)
          have h2 : (p - 1) * (q - 1) < q * (q - 1) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          omega
    rw [hpq] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hcop : Nat.Coprime (p * q) c := by
      rw [hc] at hsq
      exact Nat.coprime_of_squarefree_mul hsq
    have hcop2 : Nat.Coprime p q := (Nat.coprime_primes h.hp h.hq).mpr hne
    have hφc : Nat.totient c = 1 := by
      have e := hφ
      rw [hc, Nat.totient_mul hcop, Nat.totient_mul hcop2, Nat.totient_prime h.hp,
        Nat.totient_prime h.hq] at e
      have hpos : 0 < (p - 1) * (q - 1) := Nat.mul_pos (by omega) (by omega)
      have : (p - 1) * (q - 1) * Nat.totient c = (p - 1) * (q - 1) * 1 := by rw [e, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    rcases Nat.totient_eq_one_iff.mp hφc with hc1 | hc2
    · rw [hc, hc1, mul_one]
    · exfalso
      have e := hμ
      rw [hc, hc2, isMultiplicative_moebius.map_mul_of_coprime (hc2 ▸ hcop),
        isMultiplicative_moebius.map_mul_of_coprime hcop2, moebius_apply_prime h.hp,
        moebius_apply_prime h.hq, moebius_apply_prime Nat.prime_two] at e
      norm_num at e
  · rintro rfl
    exact r_mul_primes h.hp h.hq hne

/-- **Lemma 3.1 (iii), equality case.**  For `n = p^a` and a divisor `M > 1` of `n`,
`r M = 0` iff `M ≠ p`. -/
theorem r_eq_zero_iff_prime_pow {p a M : ℕ} (hp : p.Prime) (hM : 1 < M) (hMn : M ∣ p ^ a) :
    r M = 0 ↔ M ≠ p := by
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hMn
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hM
  constructor
  · intro h0 heq
    rw [heq, r_prime hp] at h0
    have : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      linarith
    rw [neg_div] at h0
    have : (1 : ℝ) / ((p : ℝ) - 1) > 0 := by positivity
    linarith
  · intro hne
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hne (pow_one p)
    rw [r, moebius_apply_prime_pow hp hk]
    simp [hk1]

/-! ### Counting residues of a given additive order -/

theorem card_addOrderOf_eq {n d : ℕ} [NeZero n] (hd : d ∣ n) :
    #(univ.filter (fun k : ZMod n => addOrderOf k = d)) = Nat.totient d := by
  classical
  have := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod n) (d := d) (by simpa [ZMod.card] using hd)
  simpa using this

variable {n : ℕ} [NeZero n]

theorem lapEig_eq_iff (k : ZMod n) (x : ℝ) :
    lapEig n k = (Nat.totient n : ℝ) * (1 - x) ↔ r (addOrderOf k) = x := by
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  unfold lapEig
  constructor
  · intro h
    have := mul_left_cancel₀ hφ.ne' h
    linarith
  · intro h
    rw [h]

omit [NeZero n] in
theorem lapEig_zero : lapEig n 0 = 0 := by
  unfold lapEig
  rw [addOrderOf_zero, r_one]
  ring

/-- **Theorem 3.2, multiplicity of `λ_max`.**  Exactly `p - 1` residues carry `λ_max`. -/
theorem card_lapEig_max (hn : 1 < n) :
    #(univ.filter (fun k : ZMod n =>
        lapEig n k = (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1))))
      = n.minFac - 1 := by
  classical
  have hn1 : n ≠ 1 := by omega
  have hp := Nat.minFac_prime hn1
  have hp1 : (n.minFac : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have e : (n.minFac : ℝ) / ((n.minFac : ℝ) - 1) = 1 - (-1 / ((n.minFac : ℝ) - 1)) := by
    field_simp
    ring
  have hset : univ.filter (fun k : ZMod n =>
        lapEig n k = (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1)))
      = univ.filter (fun k : ZMod n => addOrderOf k = n.minFac) := by
    ext k
    simp only [mem_filter, mem_univ, true_and]
    rw [e, lapEig_eq_iff]
    by_cases hk : k = 0
    · subst hk
      rw [addOrderOf_zero, r_one]
      constructor
      · intro h
        have : (0 : ℝ) < 1 / ((n.minFac : ℝ) - 1) := by
          have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
          have : (0 : ℝ) < (n.minFac : ℝ) - 1 := by linarith
          positivity
        rw [neg_div] at h
        linarith
      · intro h
        exact absurd h.symm hp.one_lt.ne'
    · exact r_eq_min_iff (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)
  rw [hset, card_addOrderOf_eq (Nat.minFac_dvd n), Nat.totient_prime hp]

/-- **Theorem 3.2, multiplicity of `λ₂` when `ω(n) ≥ 2`.**  Exactly `(p-1)(q-1)` residues. -/
theorem card_lapEig_two_primes {p q : ℕ} (h : TwoSmallest n p q) :
    #(univ.filter (fun k : ZMod n =>
        k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)))))
      = (p - 1) * (q - 1) := by
  classical
  have hne : p ≠ q := by have := h.hlt; omega
  have hcop : Nat.Coprime p q := (Nat.coprime_primes h.hp h.hq).mpr hne
  have hpq : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd h.hpn h.hqn
  have hset : univ.filter (fun k : ZMod n =>
        k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))))
      = univ.filter (fun k : ZMod n => addOrderOf k = p * q) := by
    ext k
    simp only [mem_filter, mem_univ, true_and]
    rw [lapEig_eq_iff]
    constructor
    · rintro ⟨hk, hr⟩
      exact (r_eq_max_iff h (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)).mp hr
    · intro hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [addOrderOf_zero] at hk
        have := Nat.mul_le_mul h.hp.two_le h.hq.two_le
        omega
      exact ⟨hk0, (r_eq_max_iff h (one_lt_addOrderOf hk0) (addOrderOf_dvd_self k)).mpr hk⟩
  rw [hset, card_addOrderOf_eq hpq, Nat.totient_mul hcop, Nat.totient_prime h.hp,
    Nat.totient_prime h.hq]

/-- **Theorem 3.2, multiplicity of `λ₂` for `n = p^a`, `a ≥ 2`.**  Exactly `p^a - p` residues. -/
theorem card_lapEig_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (hn : n = p ^ a) :
    #(univ.filter (fun k : ZMod n => k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ)))
      = p ^ a - p := by
  classical
  have hpn : p ∣ n := by
    rw [hn]
    exact dvd_pow_self p (by omega)
  have hdvd : ∀ k : ZMod n, addOrderOf k ∣ p ^ a := fun k => by
    rw [← hn]
    exact addOrderOf_dvd_self k
  have hset : univ.filter (fun k : ZMod n => k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ))
      = (univ.filter (fun k : ZMod n => addOrderOf k ≠ 1)) \
          univ.filter (fun k : ZMod n => addOrderOf k = p) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    have e : (Nat.totient n : ℝ) = (Nat.totient n : ℝ) * (1 - 0) := by ring
    rw [e, lapEig_eq_iff]
    rw [ne_eq, ← AddMonoid.addOrderOf_eq_one_iff.not]
    constructor
    · rintro ⟨hk, hr⟩
      have hk' : k ≠ 0 := fun h0 => hk (by rw [h0, addOrderOf_zero])
      exact ⟨hk, (r_eq_zero_iff_prime_pow hp (one_lt_addOrderOf hk') (hdvd k)).mp hr⟩
    · rintro ⟨hk, hkp⟩
      have hk' : k ≠ 0 := fun h0 => hk (by rw [h0, addOrderOf_zero])
      exact ⟨hk, (r_eq_zero_iff_prime_pow hp (one_lt_addOrderOf hk') (hdvd k)).mpr hkp⟩
  have hsub : univ.filter (fun k : ZMod n => addOrderOf k = p)
      ⊆ univ.filter (fun k : ZMod n => addOrderOf k ≠ 1) := by
    intro k
    simp only [mem_filter, mem_univ, true_and]
    intro hk
    rw [hk]
    exact hp.one_lt.ne'
  have hcompl : univ.filter (fun k : ZMod n => addOrderOf k ≠ 1)
      = univ \ univ.filter (fun k : ZMod n => addOrderOf k = 1) := by
    ext k
    simp
  rw [hset, card_sdiff_of_subset hsub, hcompl, card_sdiff_of_subset (subset_univ _),
    card_addOrderOf_eq (one_dvd n), card_addOrderOf_eq hpn, card_univ, ZMod.card,
    Nat.totient_one, Nat.totient_prime hp, hn]
  have : p ≤ p ^ a := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
  have := hp.two_le
  omega

/-- **Theorem 3.2, prime case.**  For `n = p` prime every `k ≠ 0` has eigenvalue `n`. -/
theorem lapEig_prime (hp : n.Prime) (k : ZMod n) (hk : k ≠ 0) : lapEig n k = n := by
  have hord : addOrderOf k = n := by
    rcases (Nat.dvd_prime hp).mp (addOrderOf_dvd_self k) with h1 | h1
    · exact absurd h1 (one_lt_addOrderOf hk).ne'
    · exact h1
  unfold lapEig
  rw [hord, r_prime hp, Nat.totient_prime hp]
  have : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    linarith
  rw [Nat.cast_sub hp.one_le]
  push_cast
  field_simp
  ring

/-! ### Corollary 3.3: the spectral ratio -/

/-- **Corollary 3.3, formula.**  `λ₂/λ_max = ((p-1)(q-1) - 1)/(p(q-1))` when `ω(n) ≥ 2`. -/
theorem spectral_ratio_formula {p q : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q) :
    (1 - 1 / ((p - 1) * (q - 1))) / (1 - (-1 / (p - 1)))
      = ((p - 1) * (q - 1) - 1) / (p * (q - 1)) := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : q - 1 ≠ 0 := by linarith
  have h3 : p ≠ 0 := by linarith
  have hA : 1 - (-1 / (p - 1)) ≠ 0 := by
    have : 1 - (-1 / (p - 1)) = p / (p - 1) := by field_simp; ring
    rw [this]
    exact div_ne_zero h3 h1
  have hB : p * (q - 1) ≠ 0 := mul_ne_zero h3 h2
  rw [div_eq_div_iff hA hB]
  field_simp
  ring

/-- **Corollary 3.3.**  For every `n ≥ 2`, `λ₂/λ_max = (1 - r_max)/(1 - r_min) ≥ 1/4`,
with equality iff `6 ∣ n`. -/
theorem spectral_ratio {m : ℕ} (hm : 2 ≤ m) {rmax rmin : ℝ} (hmax : IsGreatest (DivSet m) rmax)
    (hmin : IsLeast (DivSet m) rmin) :
    1 / 4 ≤ (1 - rmax) / (1 - rmin) ∧ ((1 - rmax) / (1 - rmin) = 1 / 4 ↔ 6 ∣ m) := by
  have hrmin := hmin.unique (isLeast_divSet hm)
  subst hrmin
  set p := m.minFac with hpdef
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : (1 : ℝ) - (-1 / ((p : ℝ) - 1)) = p / ((p : ℝ) - 1) := by
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  by_cases hpp : IsPrimePow m
  · obtain ⟨p', k, hp', hk, hpk⟩ := (isPrimePow_nat_iff m).mp hpp
    have hmin' : m.minFac = p' := by rw [← hpk]; exact Nat.Prime.pow_minFac hp' (by omega)
    have h6 : ¬ 6 ∣ m := by
      intro h6
      rw [← hpk] at h6
      have h2 : p' = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp
        (Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num) h6))).symm
      have h3 : p' = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp').mp
        (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h6))).symm
      omega
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at hpk
      subst hpk
      have hrmax := hmax.unique (isGreatest_divSet_prime hp')
      subst hrmax
      have : (1 - (-1 / ((p : ℝ) - 1))) / (1 - (-1 / ((p : ℝ) - 1))) = 1 := by
        rw [div_self]
        rw [hden]
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        positivity
      have hpeq : p = p' := hpdef.trans hmin'
      rw [hpeq] at this
      rw [hpeq, this]
      exact ⟨by norm_num, by constructor <;> intro h' <;> [norm_num at h'; exact absurd h' h6]⟩
    · rw [← hpk] at hmax
      have hrmax := hmax.unique (isGreatest_divSet_prime_pow hp' hk2)
      subst hrmax
      rw [hden, hpdef, hmin']
      have hp'2 : (2 : ℝ) ≤ p' := by exact_mod_cast hp'.two_le
      have hval : (1 - 0) / ((p' : ℝ) / ((p' : ℝ) - 1)) = ((p' : ℝ) - 1) / p' := by
        have : (p' : ℝ) - 1 ≠ 0 := by linarith
        have : (p' : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      rw [hval]
      have hgt : (1 : ℝ) / 4 < ((p' : ℝ) - 1) / p' := by
        rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
        linarith
      exact ⟨hgt.le, by constructor <;> intro h' <;> [linarith; exact absurd h' h6]⟩
  · obtain ⟨q, hts⟩ := exists_twoSmallest hm hpp
    have hrmax := hmax.unique (isGreatest_divSet_of_twoSmallest hts)
    subst hrmax
    have hq3n : 3 ≤ q := by have := hts.hp.two_le; have := hts.hlt; omega
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq3n
    rw [← hpdef, spectral_ratio_formula hp2 hq3]
    have hD : (0 : ℝ) < p * ((q : ℝ) - 1) := by nlinarith
    have h0 : 0 ≤ ((p : ℝ) - 2) * ((q : ℝ) - 3) := mul_nonneg (by linarith) (by linarith)
    refine ⟨?_, ?_⟩
    · rw [div_le_div_iff₀ (by norm_num) hD]
      nlinarith
    · constructor
      · intro heq
        rw [div_eq_div_iff hD.ne' (by norm_num)] at heq
        have hp' : (p : ℝ) = 2 := by nlinarith
        have hq' : (q : ℝ) = 3 := by nlinarith
        have hpn : p = 2 := by exact_mod_cast hp'
        have hqn : q = 3 := by exact_mod_cast hq'
        have h2 : 2 ∣ m := by
          have e : m.minFac = 2 := hpn
          rw [← e]
          exact Nat.minFac_dvd m
        have h3 : 3 ∣ m := by have := hts.hqn; rwa [hqn] at this
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
      · intro h6
        have h2 : 2 ∣ m := dvd_trans (by norm_num) h6
        have h3 : 3 ∣ m := dvd_trans (by norm_num) h6
        have hpn : p = 2 := le_antisymm (hts.least 2 Nat.prime_two h2) hts.hp.two_le
        have hqn : q = 3 := le_antisymm (hts.second 3 Nat.prime_three h3 (by omega)) hq3n
        rw [hpn, hqn]
        norm_num

end ArithmeticDynamics
