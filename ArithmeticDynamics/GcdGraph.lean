/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XVIII: gcd graphs `X_n(D)` — symmetry, the hexagonal state (Proposition 6.2), the
decomposition (2.5) of the symbol into Ramanujan sums, integrality of the spectrum and the
rationality of the consensus rate (Proposition 6.4).
-/
import Mathlib
import ArithmeticDynamics.Circulant

namespace ArithmeticDynamics

open Finset Real ArithmeticFunction

variable {n : ℕ} [NeZero n]

/-- The connection set `S_D = {s : gcd(s, n) ∈ D}` of the gcd graph `X_n(D)`. -/
def gcdSet (n : ℕ) [NeZero n] (D : Finset ℕ) : Finset (ZMod n) :=
  univ.filter (fun s : ZMod n => Nat.gcd s.val n ∈ D)

theorem gcd_val_neg (s : ZMod n) : Nat.gcd (-s).val n = Nat.gcd s.val n := by
  rw [ZMod.neg_val]
  split_ifs with h
  · rw [h]; simp
  · exact Nat.gcd_self_sub_left (ZMod.val_lt s).le

theorem gcdSet_symm (D : Finset ℕ) : IsSymm (gcdSet n D) := by
  intro s hs
  simp only [gcdSet, mem_filter, mem_univ, true_and] at hs ⊢
  rwa [gcd_val_neg]

/-! ### Proposition 6.2: the hexagonal state on gcd graphs -/

theorem cWeight_hex_gcd (h6 : 6 ∣ n) {D : Finset ℕ} (hD6 : ∀ d ∈ D, Nat.Coprime d 6)
    {s : ZMod n} (hs : s ∈ gcdSet n D) : cWeight ((n / 6 : ℕ) : ZMod n) s = 1 / 2 := by
  simp only [gcdSet, mem_filter, mem_univ, true_and] at hs
  have hc := hD6 _ hs
  have h2 : ¬ (2 : ℤ) ∣ (s.val : ℤ) := by
    intro h
    have h' : 2 ∣ s.val := by exact_mod_cast h
    have : 2 ∣ Nat.gcd s.val n := Nat.dvd_gcd h' (dvd_trans (by norm_num) h6)
    have := Nat.Coprime.coprime_dvd_left this hc
    norm_num at this
  have h3 : ¬ (3 : ℤ) ∣ (s.val : ℤ) := by
    intro h
    have h' : 3 ∣ s.val := by exact_mod_cast h
    have : 3 ∣ Nat.gcd s.val n := Nat.dvd_gcd h' (dvd_trans (by norm_num) h6)
    have := Nat.Coprime.coprime_dvd_left this hc
    norm_num at this
  obtain ⟨t, ht⟩ := h6
  have ht0 : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by rintro rfl; exact NeZero.ne n (by simpa using ht)
    exact_mod_cast this
  have hdiv : n / 6 = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by norm_num)
  unfold cWeight
  rw [natCast_mul_val, stdAddChar_natCast_re, hdiv, ← cos_hexagonal _ h2 h3]
  congr 1
  have hn : (n : ℝ) = 6 * (t : ℝ) := by exact_mod_cast ht
  rw [hn]
  push_cast
  field_simp
  ring

/-- **Proposition 6.2, Jacobian.**  `J = -(K/(2|S_D|)) L_D` at the hexagonal state. -/
theorem cJac_hex_gcd (h6 : 6 ∣ n) {D : Finset ℕ} (hD6 : ∀ d ∈ D, Nat.Coprime d 6) (K : ℝ)
    (f : ZMod n → ℝ) (i : ZMod n) :
    cJac (gcdSet n D) K ((n / 6 : ℕ) : ZMod n) f i
      = -(K / (2 * (#(gcdSet n D) : ℝ))) * cLap (gcdSet n D) f i := by
  unfold cJac cLap
  rw [sum_congr rfl fun s hs => by rw [cWeight_hex_gcd h6 hD6 hs]]
  rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos #(gcdSet n D) with h0 | hpos
  · rw [h0]; simp
  · have : (#(gcdSet n D) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
    ring

theorem cWeight_zero (s : ZMod n) : cWeight 0 s = 1 := by
  unfold cWeight
  simp

theorem cJac_sync (S : Finset (ZMod n)) (K : ℝ) (f : ZMod n → ℝ) (i : ZMod n) :
    cJac S K 0 f i = -(K / (#S : ℝ)) * cLap S f i := by
  unfold cJac cLap
  simp only [cWeight_zero, one_mul]
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

theorem nonempty_of_gen (hn : 1 < n) {S : Finset (ZMod n)}
    (hgen : AddSubgroup.closure (S : Set (ZMod n)) = ⊤) : S.Nonempty := by
  rcases S.eq_empty_or_nonempty with h | h
  · exfalso
    haveI : Fact (1 < n) := ⟨hn⟩
    have h1 : (1 : ZMod n) ∈ AddSubgroup.closure (S : Set (ZMod n)) := by rw [hgen]; trivial
    rw [h, coe_empty, AddSubgroup.closure_empty, AddSubgroup.mem_bot] at h1
    exact one_ne_zero h1
  · exact h

/-- The algebraic connectivity `λ₂ = min_{k ≠ 0} (|S| - C(k))` of a circulant, for `n ≥ 2`. -/
noncomputable def lam2 (S : Finset (ZMod n)) (hn : 1 < n) : ℝ :=
  (univ.erase (0 : ZMod n)).inf'
    ⟨1, mem_erase.mpr ⟨by haveI : Fact (1 < n) := ⟨hn⟩; exact one_ne_zero, mem_univ _⟩⟩
    (fun k => (#S : ℝ) - cSym S k)

theorem lam2_le (S : Finset (ZMod n)) (hn : 1 < n) (k : ZMod n) (hk : k ≠ 0) :
    lam2 S hn ≤ (#S : ℝ) - cSym S k :=
  inf'_le _ (mem_erase.mpr ⟨hk, mem_univ _⟩)

theorem lam2_pos {S : Finset (ZMod n)} (hn : 1 < n)
    (hgen : AddSubgroup.closure (S : Set (ZMod n)) = ⊤) : 0 < lam2 S hn := by
  obtain ⟨k, hk, he⟩ := exists_mem_eq_inf' (s := univ.erase (0 : ZMod n))
    ⟨1, mem_erase.mpr ⟨by haveI : Fact (1 < n) := ⟨hn⟩; exact one_ne_zero, mem_univ _⟩⟩
    (fun k => (#S : ℝ) - cSym S k)
  unfold lam2
  rw [he]
  exact cLap_eig_pos hgen k (ne_of_mem_erase hk)

/-- **Proposition 6.2.**  If `6 ∣ n`, every `d ∈ D` is coprime to `6` and `X_n(D)` is connected,
the hexagonal state is exponentially stable modulo rotation with every rate below
`K λ₂(L_D)/(2|S_D|)`, and `λ₂(L_D) > 0`. -/
theorem gcd_hex_expStable (hL : LyapunovIndirectStability n) (h6 : 6 ∣ n) {D : Finset ℕ}
    (hD6 : ∀ d ∈ D, Nat.Coprime d 6)
    (hgen : AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) = ⊤)
    {K : ℝ} (hK : 0 < K) (hn : 1 < n) :
    0 < lam2 (gcdSet n D) hn ∧
      ∀ r', 0 < r' → r' < K * lam2 (gcdSet n D) hn / (2 * (#(gcdSet n D) : ℝ)) →
        ExpStableOnLevel (cField (gcdSet n D) K) (twisted n (n / 6)) r' := by
  set S := gcdSet n D
  have hlam := lam2_pos hn hgen
  have hSne := nonempty_of_gen hn hgen
  have hS0 : (0 : ℝ) < #S := by exact_mod_cast hSne.card_pos
  refine ⟨hlam, fun r' hr' hr => ?_⟩
  refine hL _ _ (K * lam2 S hn / (2 * #S)) (contDiff_cField K) (lipschitz_cField K)
    (cField_twisted (gcdSet_symm D) K _) (sum_cField (gcdSet_symm D) K) (by positivity)
    (fun w hw => ?_) r' hr' hr
  simp_rw [fderiv_cField_twisted, cJac_hex_gcd h6 hD6, mul_assoc, ← mul_sum]
  have hq := cLap_quad_lower (gcdSet_symm D) w hw (fun k hk => lam2_le S hn k hk)
  have hc : 0 ≤ K / (2 * (#S : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  have e : K / (2 * (#S : ℝ)) * (lam2 S hn * sqNorm w) = K * lam2 S hn / (2 * #S) * sqNorm w := by
    field_simp
  linarith

/-- **Proposition 6.2, synchronous state.**  On a connected gcd graph the synchronous state is
exponentially stable modulo rotation with every rate below `K λ₂(L_D)/|S_D|` (twice the
hexagonal bound). -/
theorem gcd_sync_expStable (hL : LyapunovIndirectStability n) {D : Finset ℕ}
    (hgen : AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) = ⊤)
    {K : ℝ} (hK : 0 < K) (hn : 1 < n) :
    ∀ r', 0 < r' → r' < K * lam2 (gcdSet n D) hn / (#(gcdSet n D) : ℝ) →
      ExpStableOnLevel (cField (gcdSet n D) K) (twisted n 0) r' := by
  set S := gcdSet n D
  have hlam := lam2_pos hn hgen
  have hSne := nonempty_of_gen hn hgen
  have hS0 : (0 : ℝ) < #S := by exact_mod_cast hSne.card_pos
  intro r' hr' hr
  refine hL _ _ (K * lam2 S hn / #S) (contDiff_cField K) (lipschitz_cField K)
    (cField_twisted (gcdSet_symm D) K _) (sum_cField (gcdSet_symm D) K) (by positivity)
    (fun w hw => ?_) r' hr' hr
  simp_rw [fderiv_cField_twisted]
  have h0 : ((0 : ℕ) : ZMod n) = 0 := Nat.cast_zero
  rw [h0]
  simp_rw [cJac_sync, mul_assoc, ← mul_sum]
  have hq := cLap_quad_lower (gcdSet_symm D) w hw (fun k hk => lam2_le S hn k hk)
  have hc : 0 ≤ K / (#S : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  have e : K / (#S : ℝ) * (lam2 S hn * sqNorm w) = K * lam2 S hn / #S * sqNorm w := by
    field_simp
  linarith

/-! ### Equation (2.5) and Proposition 6.4 -/

/-- **Equation (2.5).**  For `d ∣ n`, the sum of `e(ks/n)` over `gcd(s, n) = d` is the Ramanujan
sum `c_{n/d}(k)`. -/
theorem fiber_sum_eq_ramanujan {d : ℕ} (hd : d ∣ n) (hd0 : 0 < d) [NeZero (n / d)] (k : ZMod n) :
    ∑ s ∈ univ.filter (fun s : ZMod n => Nat.gcd s.val n = d), (ZMod.stdAddChar (k * s) : ℂ)
      = ramanujan (n / d) ((k.val : ℕ) : ZMod (n / d)) := by
  set N := n / d with hN
  have hnd : n = d * N := (Nat.mul_div_cancel' hd).symm
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hlt : ∀ x : ℕ, x < N → d * x < n := fun x hx =>
    lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left hx hd0) hnd.symm
  have hgcd : ∀ x : ℕ, Nat.gcd (d * x) n = d * Nat.gcd x N := fun x => by
    rw [hnd, Nat.gcd_mul_left]
  have hndR : (n : ℝ) = d * N := by exact_mod_cast hnd
  unfold ramanujan
  symm
  refine sum_bij (fun t _ => ((d * (t : ZMod N).val : ℕ) : ZMod n)) ?_ ?_ ?_ ?_
  · intro t _
    simp only [mem_filter, mem_univ, true_and]
    rw [ZMod.val_natCast_of_lt (hlt _ (ZMod.val_lt _)), hgcd, ZMod.val_coe_unit_coprime, mul_one]
  · intro a _ b _ hab
    have := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (hlt _ (ZMod.val_lt _)),
      ZMod.val_natCast_of_lt (hlt _ (ZMod.val_lt _))] at this
    exact Units.ext (ZMod.val_injective N (Nat.eq_of_mul_eq_mul_left hd0 this))
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    obtain ⟨t0, ht0⟩ : d ∣ s.val := hs ▸ Nat.gcd_dvd_left s.val n
    have ht0N : t0 < N := by
      have h1 := ZMod.val_lt s
      rw [ht0] at h1
      have h2 : d * t0 < d * N := lt_of_lt_of_eq h1 hnd
      exact Nat.lt_of_mul_lt_mul_left h2
    have hcop : Nat.Coprime t0 N := by
      have e : Nat.gcd (d * t0) n = d := by rw [← ht0]; exact hs
      rw [hgcd] at e
      have : d * Nat.gcd t0 N = d * 1 := by rw [e, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hd0 this
    refine ⟨ZMod.unitOfCoprime t0 hcop, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt ht0N, ← ht0, ZMod.natCast_zmod_val]
  · intro t _
    have hk : k * ((d * (t : ZMod N).val : ℕ) : ZMod n)
        = ((k.val * (d * (t : ZMod N).val) : ℕ) : ZMod n) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hdiv : ((n / d : ℕ) : ℝ) = (n : ℝ) / d := Nat.cast_div hd hd'
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have hreal : 2 * π * ((k.val * (t : ZMod (n / d)).val : ℕ) : ℝ) / ((n / d : ℕ) : ℝ)
        = 2 * π * ((k.val * (d * (t : ZMod (n / d)).val) : ℕ) : ℝ) / (n : ℝ) := by
      rw [hdiv]
      push_cast
      field_simp
    rw [natCast_mul_val, hk, stdAddChar_natCast, stdAddChar_natCast, hreal]

/-- Ramanujan sums are integers. -/
theorem ramanujan_int (N : ℕ) [NeZero N] (j : ZMod N) : ∃ z : ℤ, ramanujan N j = z := by
  set M := addOrderOf j
  have hM : 0 < M := addOrderOf_pos j
  have hdvd : Nat.totient M ∣ Nat.totient N :=
    Nat.totient_dvd_of_dvd (by have := addOrderOf_dvd_card (x := j); rwa [ZMod.card] at this)
  obtain ⟨c, hc⟩ := hdvd
  have hφM : (Nat.totient M : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hM).ne'
  refine ⟨c * moebius M, ?_⟩
  rw [ramanujan_eq, r, hc]
  have hMj : addOrderOf j = M := rfl
  rw [hMj]
  push_cast
  rw [mul_div_assoc', div_eq_iff hφM]
  ring

/-- **Integrality.**  Every value `C_{S_D}(k)` of the symbol of a gcd graph is an integer. -/
theorem cSym_gcd_int (D : Finset ℕ) (k : ZMod n) : ∃ z : ℤ, cSym (gcdSet n D) k = z := by
  have hsplit : ∑ s ∈ gcdSet n D, (ZMod.stdAddChar (k * s) : ℂ)
      = ∑ d ∈ D, ∑ s ∈ univ.filter (fun s : ZMod n => Nat.gcd s.val n = d),
          (ZMod.stdAddChar (k * s) : ℂ) := by
    rw [← sum_fiberwise_of_maps_to (s := gcdSet n D) (t := D) (g := fun s => Nat.gcd s.val n)
      (fun s hs => (mem_filter.mp hs).2)]
    refine sum_congr rfl fun d hd => ?_
    congr 1
    ext s
    simp only [gcdSet, mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hd, h⟩
  have hfib : ∀ d, ∃ z : ℤ, ∑ s ∈ univ.filter (fun s : ZMod n => Nat.gcd s.val n = d),
      (ZMod.stdAddChar (k * s) : ℂ) = z := by
    intro d
    by_cases hd : d ∣ n ∧ 0 < d
    · obtain ⟨hdn, hd0⟩ := hd
      haveI : NeZero (n / d) := ⟨by
        have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hdn) hd0
        omega⟩
      rw [fiber_sum_eq_ramanujan hdn hd0]
      exact ramanujan_int _ _
    · refine ⟨0, ?_⟩
      push_cast
      refine sum_eq_zero fun s hs => ?_
      exfalso
      simp only [mem_filter, mem_univ, true_and] at hs
      apply hd
      refine ⟨hs ▸ Nat.gcd_dvd_right _ _, ?_⟩
      rw [← hs]
      exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne n))
  choose z hz using hfib
  refine ⟨∑ d ∈ D, z d, ?_⟩
  have h := cSym_eq (gcdSet_symm D) k
  rw [hsplit, sum_congr rfl fun d _ => hz d] at h
  push_cast at h
  exact_mod_cast h

/-- **Extreme eigenvalues of a gcd graph** (used in Proposition 6.4).  For every gcd graph
`X_n(D)`, `n ≥ 2`, with `C⁺ = max_{k≠0} C(k)` and `C⁻ = min_{k≠0} C(k)`, every non-trivial
Laplacian eigenvalue `|S| - C(k)` lies in `[|S| - C⁺, |S| - C⁻]`, both ends are attained, the
quotient `(λ_max - λ₂)/(λ_max + λ₂)` equals `(C⁺ - C⁻)/(2|S| - C⁺ - C⁻)`, and this number is
rational.  No connectivity is assumed here; the dynamical statements, which do need it, are
`gcd_consensus` (connected) and `gcd_no_consensus` (disconnected) in `GcdConsensus.lean`. -/
theorem gcd_rate (D : Finset ℕ) (hn : 1 < n) :
    let S := gcdSet n D
    let ne : (univ.erase (0 : ZMod n)).Nonempty :=
      ⟨1, mem_erase.mpr ⟨by haveI : Fact (1 < n) := ⟨hn⟩; exact one_ne_zero, mem_univ _⟩⟩
    let Cp := (univ.erase (0 : ZMod n)).sup' ne (cSym S)
    let Cm := (univ.erase (0 : ZMod n)).inf' ne (cSym S)
    (∀ k : ZMod n, k ≠ 0 →
        (#S : ℝ) - Cp ≤ (#S : ℝ) - cSym S k ∧ (#S : ℝ) - cSym S k ≤ (#S : ℝ) - Cm) ∧
      (∃ k, k ≠ 0 ∧ cSym S k = Cp) ∧ (∃ k, k ≠ 0 ∧ cSym S k = Cm) ∧
      (((#S : ℝ) - Cm) - ((#S : ℝ) - Cp)) / (((#S : ℝ) - Cm) + ((#S : ℝ) - Cp))
        = (Cp - Cm) / (2 * #S - Cp - Cm) ∧
      ∃ q : ℚ, (Cp - Cm) / (2 * (#S : ℝ) - Cp - Cm) = q := by
  intro S ne Cp Cm
  obtain ⟨kp, hkp, hp⟩ := exists_mem_eq_sup' ne (cSym S)
  obtain ⟨km, hkm, hm⟩ := exists_mem_eq_inf' ne (cSym S)
  refine ⟨fun k hk => ⟨?_, ?_⟩, ⟨kp, ne_of_mem_erase hkp, hp.symm⟩,
    ⟨km, ne_of_mem_erase hkm, hm.symm⟩, by ring_nf, ?_⟩
  · have := le_sup' (cSym S) (mem_erase.mpr ⟨hk, mem_univ k⟩)
    linarith
  · have := inf'_le (cSym S) (mem_erase.mpr ⟨hk, mem_univ k⟩)
    linarith
  · obtain ⟨zp, hzp⟩ := cSym_gcd_int D kp
    obtain ⟨zm, hzm⟩ := cSym_gcd_int D km
    refine ⟨(zp - zm) / (2 * #S - zp - zm), ?_⟩
    simp only [Cp, Cm]
    rw [hp, hm, hzp, hzm]
    push_cast
    ring

end ArithmeticDynamics
