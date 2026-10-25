-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.SingleScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_thin_tubes_bootstrap.Removal
import Submission.WZ.Obl.wz_osw_thin_tubes_bootstrap.Numerics

/-!
# From a single-scale heavy-pair estimate to the bootstrapping step

`SingleScaleAt ε τ θ η r₀` says: at every scale `r ≤ r₀`, for `(δ,1,C)`-Frostman
`G, G'` at distance `≥ 1/4` and a relation `E ⊆ G ×ˢ G'` which is
`(σ, K)`-thin (with `C, K ≤ r ^ (-η)`), the pairs of `E` lying in a strip of
half-width `r` with at least `r ^ (σ + τ) * #G'` points of `E` number at most
`r ^ θ * #G * #G'`.  `one_direction` turns it into the thin-tubes improvement
of one ordered pair, by heavy-strip removal at the dyadic scales.
-/

namespace WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap

/-- The frozen Frostman predicate. -/
def Frost (δ C : ℝ) (X : Set E2) : Prop :=
  X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧
    ∀ (x : E2) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard

/-- Pairs of `E` lying in a strip of half-width `r` through their first point that
contains at least `r ^ (σ + τ) * #G'` points of `E`. -/
def p2Heavy (E : Set (E2 × E2)) (r σ τ : ℝ) (G' : Set E2) : Set (E2 × E2) :=
  {q | q ∈ E ∧ ∃ e : E2, ‖e‖ = 1 ∧ |inner ℝ (q.2 - q.1) e| < r ∧
    r ^ (σ + τ) * G'.ncard ≤ ({b' | (q.1, b') ∈ E ∧ |inner ℝ (b' - q.1) e| < r}.ncard : ℝ)}

/-- The single-scale heavy-pair estimate, unpacked at a fixed `ε`. -/
def SingleScaleAt (ε τ θ η r₀ : ℝ) : Prop :=
  ∀ δ r σ K C : ℝ, 0 < δ → δ ≤ r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε →
    1 ≤ K → K ≤ r ^ (-η) → 1 ≤ C → C ≤ r ^ (-η) →
    ∀ G G' : Set E2, Frost δ C G → Frost δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') →
    ∀ E : Set (E2 × E2), E ⊆ G ×ˢ G' →
    (∀ b ∈ G, ∀ e : E2, ‖e‖ = 1 → ∀ ρ : ℝ, δ ≤ ρ →
      ({b' | (b, b') ∈ E ∧ |inner ℝ (b' - b) e| < ρ}.ncard : ℝ) ≤ K * ρ ^ σ * G'.ncard) →
    ((p2Heavy E r σ τ G').ncard : ℝ) ≤ r ^ θ * G.ncard * G'.ncard

/-- A strip heavy for the removal threshold is heavy for the single-scale threshold. -/
lemma heavyPairs_subset_p2Heavy {T : Set (E2 × E2)} {G' : Set E2} {d K' σ τ τ₀ : ℝ}
    (hd : 0 < d) (hρ1 : 2 * d ≤ 1) (hττ₀ : τ ≤ τ₀)
    (hστ : σ + τ ≤ 2) (hK' : 4 ≤ K') :
    heavyPairs T (2 * d) (K' * d ^ (σ + τ) * G'.ncard) ⊆ p2Heavy T (2 * d) σ τ₀ G' := by
  rintro q ⟨hqT, e, he, hin, hlt⟩
  refine ⟨hqT, e, he, hin, ?_⟩
  have hρ0 : 0 < 2 * d := by linarith
  have e1 : (2 * d) ^ (σ + τ₀) ≤ (2 * d) ^ (σ + τ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by linarith)
  have e2 : (2 * d) ^ (σ + τ) = 2 ^ (σ + τ) * d ^ (σ + τ) :=
    Real.mul_rpow (by norm_num) hd.le
  have e3 : (2 : ℝ) ^ (σ + τ) ≤ 4 := by
    calc (2 : ℝ) ^ (σ + τ) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hστ
      _ = 4 := by norm_num
  have hdd : 0 ≤ d ^ (σ + τ) := Real.rpow_nonneg hd.le _
  have e4 : (2 * d) ^ (σ + τ₀) ≤ K' * d ^ (σ + τ) := by
    calc (2 * d) ^ (σ + τ₀) ≤ 2 ^ (σ + τ) * d ^ (σ + τ) := e1.trans e2.le
      _ ≤ K' * d ^ (σ + τ) := mul_le_mul_of_nonneg_right (e3.trans hK') hdd
  have hG'0 : (0 : ℝ) ≤ G'.ncard := Nat.cast_nonneg _
  exact (mul_le_mul_of_nonneg_right e4 hG'0).trans hlt.le

/-- No strip is heavy at a scale where the thin bound is below the threshold. -/
lemma heavyPairs_eq_empty {T : Set (E2 × E2)} {G G' : Set E2} {δ σ τ K K' d : ℝ}
    (hT : T ⊆ G ×ˢ G')
    (hthin : ∀ b ∈ G, ∀ e : E2, ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r →
      ({b' | (b, b') ∈ T ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤ K * r ^ σ * G'.ncard)
    (hd : 0 < d) (hδd : δ ≤ 2 * d) (hσ1 : σ ≤ 1) (hK : 0 ≤ K)
    (hbig : 2 * K ≤ K' * d ^ τ) :
    heavyPairs T (2 * d) (K' * d ^ (σ + τ) * G'.ncard) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro q ⟨hqT, e, he, hin, hlt⟩
  have hb : q.1 ∈ G := (hT hqT).1
  have hcount := hthin q.1 hb e he (2 * d) hδd
  have hlt' : K' * d ^ (σ + τ) * G'.ncard < K * (2 * d) ^ σ * G'.ncard :=
    lt_of_lt_of_le hlt hcount
  have hG'0 : (0 : ℝ) ≤ G'.ncard := Nat.cast_nonneg _
  have hlt2 : K' * d ^ (σ + τ) < K * (2 * d) ^ σ :=
    lt_of_mul_lt_mul_right hlt' hG'0
  rw [Real.rpow_add hd, Real.mul_rpow (by norm_num) hd.le] at hlt2
  have hσpos : 0 < d ^ σ := Real.rpow_pos_of_pos hd _
  have hlt3 : K' * d ^ τ < K * 2 ^ σ := by
    have : (K' * d ^ τ) * d ^ σ < (K * 2 ^ σ) * d ^ σ := by
      calc (K' * d ^ τ) * d ^ σ = K' * (d ^ σ * d ^ τ) := by ring
        _ < K * (2 ^ σ * d ^ σ) := hlt2
        _ = (K * 2 ^ σ) * d ^ σ := by ring
    exact lt_of_mul_lt_mul_right this hσpos.le
  have h2σ : (2 : ℝ) ^ σ ≤ 2 := by
    calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
      _ = 2 := Real.rpow_one 2
  have : K * 2 ^ σ ≤ K * 2 := mul_le_mul_of_nonneg_left h2σ hK
  linarith

lemma two_pow_mul_ge {δ : ℝ} (hδ : 0 < δ) (j : ℕ) : δ ≤ 2 * (2 ^ j * δ) := by
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have : δ ≤ 2 ^ j * δ := le_mul_of_one_le_left hδ.le h1
  linarith

set_option maxHeartbeats 1000000 in
/-- The bootstrapping step for one ordered pair, from the single-scale estimate. -/
theorem one_direction {ε τ₀ θ η r₀ : ℝ} (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hθ : 0 < θ) (hη : 0 < η)
    (hr₀ : 0 < r₀) (hSS : SingleScaleAt ε τ₀ θ η r₀) :
    ∃ τ M : ℝ, 0 < τ ∧ 1 ≤ M ∧ ∀ δ σ c K C : ℝ, 0 < δ → 1 / 4 ≤ σ → σ ≤ 1 - ε →
      0 < c → c < 1 / 10 → 1 ≤ K → 1 ≤ C →
      ∀ G G' : Set E2, Frost δ C G → Frost δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') →
      ∀ T : Set (E2 × E2), T ⊆ G ×ˢ G' → (1 - c) * G.ncard * G'.ncard ≤ (T.ncard : ℝ) →
      (∀ b ∈ G, ∀ e : E2, ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r →
        ({b' | (b, b') ∈ T ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤ K * r ^ σ * G'.ncard) →
      ∃ T' : Set (E2 × E2), T' ⊆ G ×ˢ G' ∧ (1 - 4 * c) * G.ncard * G'.ncard ≤ (T'.ncard : ℝ) ∧
        ∀ b ∈ G, ∀ e : E2, ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r →
          ({b' | (b, b') ∈ T' ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤
            (C * K / c) ^ M * r ^ (σ + τ) * G'.ncard := by
  classical
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = min τ₀ 1 := ⟨_, rfl⟩
  have hτ : 0 < τ := hτdef ▸ lt_min hτ₀ one_pos
  have hττ₀ : τ ≤ τ₀ := hτdef ▸ min_le_left _ _
  have hτ1 : τ ≤ 1 := hτdef ▸ min_le_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 4 * 2 ^ τ⁻¹ := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; positivity
  have hm : 0 < min r₀ 1 := lt_min hr₀ one_pos
  have hq : (1 : ℝ) < 2 ^ θ := Real.one_lt_rpow (by norm_num) hθ
  obtain ⟨u₁, hu₁0, hu₁⟩ := exists_large_exp hA hm one_pos
  obtain ⟨u₂, hu₂0, hu₂⟩ := exists_large_exp hA one_pos hη
  obtain ⟨u₃, hu₃0, hu₃⟩ := exists_large_exp hA (by linarith : (0 : ℝ) < 3 * (2 ^ θ - 1)) hθ
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = max u₁ (max u₂ u₃) := ⟨_, rfl⟩
  have hu1 : u₁ ≤ u := hudef ▸ le_max_left _ _
  have hu2 : u₂ ≤ u := hudef ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hu3 : u₃ ≤ u := hudef ▸ (le_max_right _ _).trans (le_max_right _ _)
  have hu0 : 0 ≤ u := hu₁0.trans hu1
  refine ⟨τ, 1 + τ * u, hτ, by nlinarith, ?_⟩
  intro δ σ c K C hδ hσ1 hσ2 hc hc1 hK hC G G' hG hG' hsep T hT hdense hthin
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = C * K / c := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + τ * u := ⟨_, rfl⟩
  rw [← hXdef, ← hMdef]
  have hCK : 1 ≤ C * K := by nlinarith
  have hX10 : 10 ≤ X := by
    rw [hXdef, le_div_iff₀ hc]; nlinarith
  have hX0 : 0 < X := by linarith
  have hKX : K ≤ X := by
    rw [hXdef, le_div_iff₀ hc]; nlinarith
  have hCX : C ≤ X := by
    rw [hXdef, le_div_iff₀ hc]; nlinarith
  have hXinv : X⁻¹ ≤ c := by
    rw [hXdef, inv_div, div_le_iff₀ (by positivity)]; nlinarith
  have hM1 : 1 ≤ M := by rw [hMdef]; nlinarith
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = X ^ M := ⟨_, rfl⟩
  rw [← hK'def]
  have hK'X : X ≤ K' := hK'def ▸ Real.self_le_rpow_of_one_le (by linarith) hM1
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 ^ τ⁻¹ * X ^ (-u) := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have h4R : 4 * R = A * X ^ (-u) := by rw [hRdef, hAdef]; ring
  have hR1 : 4 * R ≤ min r₀ 1 := by
    have h := hu₁ u hu1 X (by linarith)
    rw [Real.rpow_one] at h
    rw [h4R]
    calc A * X ^ (-u) ≤ min r₀ 1 * X⁻¹ := h
      _ ≤ min r₀ 1 * 1 := by
          apply mul_le_mul_of_nonneg_left _ hm.le
          exact inv_le_one_of_one_le₀ (by linarith)
      _ = min r₀ 1 := mul_one _
  have hR2 : (4 * R) ^ η ≤ X⁻¹ := by
    have h := hu₂ u hu2 X (by linarith)
    rw [h4R]; rw [one_mul] at h; exact h
  have hR3 : (4 * R) ^ θ ≤ 3 * (2 ^ θ - 1) * X⁻¹ := by
    have h := hu₃ u hu3 X (by linarith)
    rw [h4R]; exact h
  have hRτ : R ^ τ = 2 * X ^ (1 - M) := by
    rw [hRdef, Real.mul_rpow (by positivity) (by positivity),
      Real.rpow_inv_rpow (by norm_num) hτ.ne', ← Real.rpow_mul hX0.le]
    congr 2
    rw [hMdef]; ring
  have hK'R : 2 * X ≤ K' * R ^ τ := by
    rw [hRτ, hK'def, mul_left_comm, ← Real.rpow_add hX0]
    have : M + (1 - M) = 1 := by ring
    rw [this, Real.rpow_one]
  -- the dyadic cut-off
  have hex : ∃ j : ℕ, R ≤ 2 ^ j * δ := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / δ) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by rw [div_lt_iff₀ hδ] at hn; exact hn.le⟩
  set N := Nat.find hex with hNdef
  have hG'0 : (0 : ℝ) ≤ G'.ncard := Nat.cast_nonneg _
  have hTfin : T.Finite := (hG.1.prod hG'.1).subset hT
  apply thin_of_heavy_bounds hδ (by linarith) (by linarith) hG.1 hG'.1 hT hdense
    (fun j => (2 * dyad δ j) ^ θ) N
  · -- the single-scale bound at the scales below the cut-off
    intro j hj
    have hjR : dyad δ j < R := by
      have := Nat.find_min hex hj
      unfold dyad; exact not_le.mp this
    have hdpos : 0 < dyad δ j := by unfold dyad; positivity
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = 2 * dyad δ j := ⟨_, rfl⟩
    have hρ0 : 0 < ρ := by rw [hρdef]; positivity
    have hρ4R : ρ ≤ 4 * R := by rw [hρdef]; linarith
    have hρr₀ : ρ ≤ r₀ := hρ4R.trans (hR1.trans (min_le_left _ _))
    have hρ1 : ρ ≤ 1 := hρ4R.trans (hR1.trans (min_le_right _ _))
    have hδρ : δ ≤ ρ := by rw [hρdef]; unfold dyad; exact two_pow_mul_ge hδ j
    have hρη : X ≤ ρ ^ (-η) := by
      have h1 : ρ ^ η ≤ (4 * R) ^ η := Real.rpow_le_rpow hρ0.le hρ4R hη.le
      have h2 : ρ ^ η ≤ X⁻¹ := h1.trans hR2
      rw [Real.rpow_neg hρ0.le]
      have h3 : 0 < ρ ^ η := Real.rpow_pos_of_pos hρ0 _
      rw [le_inv_comm₀ hX0 h3]; exact h2
    have hmain := hSS δ ρ σ K C hδ hδρ hρr₀ hσ1 hσ2 hK (hKX.trans hρη) hC (hCX.trans hρη)
      G G' hG hG' hsep T hT hthin
    show _ ≤ (2 * dyad δ j) ^ θ * _ * _
    rw [← hρdef]
    refine le_trans ?_ hmain
    have hsub : heavyPairs T ρ (K' * dyad δ j ^ (σ + τ) * G'.ncard) ⊆ p2Heavy T ρ σ τ₀ G' := by
      rw [hρdef]
      exact heavyPairs_subset_p2Heavy hdpos (hρdef ▸ hρ1) hττ₀ (by linarith) (by linarith)
    have hfin : (p2Heavy T ρ σ τ₀ G').Finite := hTfin.subset (fun q hq => hq.1)
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  · -- no heavy strips at or above the cut-off
    intro j hj
    have hRj : R ≤ dyad δ j := by
      have h1 := Nat.find_spec hex
      unfold dyad
      have : (2 : ℝ) ^ N ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
      calc R ≤ 2 ^ N * δ := h1
        _ ≤ 2 ^ j * δ := mul_le_mul_of_nonneg_right this hδ.le
    have hdpos : 0 < dyad δ j := hR0.trans_le hRj
    have hRτj : R ^ τ ≤ dyad δ j ^ τ := Real.rpow_le_rpow hR0.le hRj hτ.le
    have hK'0 : 0 ≤ K' := by linarith
    have hbig : 2 * K ≤ K' * dyad δ j ^ τ := by
      have : K' * R ^ τ ≤ K' * dyad δ j ^ τ := mul_le_mul_of_nonneg_left hRτj hK'0
      linarith
    exact heavyPairs_eq_empty hT hthin hdpos (by unfold dyad; exact two_pow_mul_ge hδ j)
      (by linarith) (by linarith) hbig
  · -- the budget
    have hsum := sum_dyad_rpow_le hδ hθ N
    simp only [dyad] at hsum ⊢
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN]; simp; linarith
    · obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      have hnR : 2 ^ n * δ < R := by
        have := Nat.find_min hex (show n < N by omega)
        exact not_le.mp this
      have htop : 2 * (2 ^ N * δ) ≤ 4 * R := by
        rw [hn, pow_succ]
        have : 2 * (2 ^ n * 2 * δ) = 4 * (2 ^ n * δ) := by ring
        rw [this]; linarith
      have htopθ : (2 * (2 ^ N * δ)) ^ θ ≤ (4 * R) ^ θ :=
        Real.rpow_le_rpow (by positivity) htop hθ.le
      have hq1 : 0 < (2 : ℝ) ^ θ - 1 := by linarith
      calc ∑ j ∈ Finset.range N, (2 * (2 ^ j * δ)) ^ θ ≤ (2 * (2 ^ N * δ)) ^ θ / (2 ^ θ - 1) := hsum
        _ ≤ (4 * R) ^ θ / (2 ^ θ - 1) := div_le_div_of_nonneg_right htopθ hq1.le
        _ ≤ 3 * (2 ^ θ - 1) * X⁻¹ / (2 ^ θ - 1) := div_le_div_of_nonneg_right hR3 hq1.le
        _ = 3 * X⁻¹ := by field_simp
        _ ≤ 3 * c := by linarith

end WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap
