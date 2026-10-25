-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormLevels
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TopScale

/-!
# Core of the normalization: the zoomed family is dense with all-scale covers

From a family at scale `δ` with error `η` (dense, with separated all-scale covers) we choose the
zoom centre, finitely many levels of original covers, colour all conflicts, select and prune;
the resulting zoomed family at scale `lam δ` satisfies o060's `Dense` and `Weak` with error `η₁`,
provided the explicit smallness conditions on `δ` below hold.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_mem)

/-- Zoomed level targets. -/
noncomputable def levelTarget (δ' η₁ : ℝ) (m : ℕ) : ℝ :=
  min (25 * δ' * (δ' ^ (-(η₁ / 2))) ^ m) (δ' ^ η₁)

/-- The pruning retention. -/
noncomputable def normRet (δ η lam : ℝ) (L : ℕ) : ℝ :=
  δ ^ (2 * η) / (2 * 10 ^ 14 * lam ^ 2 * (normColors lam : ℝ) ^ (L + 1) * (L + 1 : ℕ))

theorem levelTarget_le {δ' η₁ : ℝ} (m : ℕ) : levelTarget δ' η₁ m ≤ δ' ^ η₁ := min_le_right _ _

theorem levelTarget_ge {δ' η₁ : ℝ} (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1) (hη₁ : 0 ≤ η₁)
    (h25 : 25 * δ' ≤ δ' ^ η₁) (m : ℕ) : 25 * δ' ≤ levelTarget δ' η₁ m := by
  apply le_min _ h25
  have hB : 1 ≤ δ' ^ (-(η₁ / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ' hδ'1 (by linarith)
  have : (1 : ℝ) ≤ (δ' ^ (-(η₁ / 2))) ^ m := one_le_pow₀ hB
  nlinarith

/-- The levels and the top cover cover every zoomed scale. -/
theorem scales_net {δ δ' η η₁ lam : ℝ} {L : ℕ} (ρ : Fin L → ℝ) (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1)
    (hη₁ : 0 < η₁) (hL : 0 < L)
    (hρlo : ∀ m : Fin L, levelTarget δ' η₁ m ≤ lam * (25 * ρ m))
    (hρhi : ∀ m : Fin L, lam * (25 * ρ m) ≤ δ ^ (-η) * levelTarget δ' η₁ m)
    (h25 : 25 * δ' ≤ δ' ^ η₁)
    (htop : δ' ^ η₁ ≤ 25 * δ' * (δ' ^ (-(η₁ / 2))) ^ (L - 1))
    (hB : δ ^ (-η) * δ' ^ (-(η₁ / 2)) ≤ δ' ^ (-η₁))
    (h25b : 25 * δ ^ (-η) ≤ δ' ^ (-η₁)) (hδη : 0 ≤ δ ^ (-η)) :
    ∀ r : ℝ, δ' ≤ r → r ≤ 1 →
      (∃ m, r ≤ lam * (25 * ρ m) ∧ lam * (25 * ρ m) ≤ δ' ^ (-η₁) * r) ∨ 1 ≤ δ' ^ (-η₁) * r := by
  intro r hr hr1
  have hpow : δ' ^ (-η₁) * δ' ^ η₁ = 1 := by
    rw [← Real.rpow_add hδ']; simp
  have hBpos : 0 < δ' ^ (-(η₁ / 2)) := Real.rpow_pos_of_pos hδ' _
  have hδ'η : 0 < δ' ^ (-η₁) := Real.rpow_pos_of_pos hδ' _
  by_cases htopr : δ' ^ η₁ ≤ r
  · right
    calc (1 : ℝ) = δ' ^ (-η₁) * δ' ^ η₁ := hpow.symm
      _ ≤ δ' ^ (-η₁) * r := mul_le_mul_of_nonneg_left htopr hδ'η.le
  push Not at htopr
  left
  by_cases hr25 : r ≤ 25 * δ'
  · refine ⟨⟨0, hL⟩, ?_, ?_⟩
    · have h0 : levelTarget δ' η₁ 0 = 25 * δ' := by
        simp only [levelTarget, pow_zero, mul_one]; exact min_eq_left h25
      have := hρlo ⟨0, hL⟩
      simp only at this
      rw [h0] at this
      linarith
    · have h0 : levelTarget δ' η₁ 0 = 25 * δ' := by
        simp only [levelTarget, pow_zero, mul_one]; exact min_eq_left h25
      have := hρhi ⟨0, hL⟩
      simp only at this
      rw [h0] at this
      calc lam * (25 * ρ ⟨0, hL⟩) ≤ δ ^ (-η) * (25 * δ') := this
        _ = (25 * δ ^ (-η)) * δ' := by ring
        _ ≤ δ' ^ (-η₁) * δ' := mul_le_mul_of_nonneg_right h25b hδ'.le
        _ ≤ δ' ^ (-η₁) * r := mul_le_mul_of_nonneg_left hr hδ'η.le
  push Not at hr25
  classical
  have hP : ∃ m, r ≤ levelTarget δ' η₁ m := by
    refine ⟨L - 1, ?_⟩
    have : levelTarget δ' η₁ (L - 1) = δ' ^ η₁ := by
      simp only [levelTarget]; exact min_eq_right htop
    rw [this]; exact htopr.le
  set m₀ := Nat.find hP with hm₀
  have hm₀P : r ≤ levelTarget δ' η₁ m₀ := Nat.find_spec hP
  have hm₀L : m₀ < L := by
    have : m₀ ≤ L - 1 := Nat.find_min' hP (by
      have : levelTarget δ' η₁ (L - 1) = δ' ^ η₁ := by
        simp only [levelTarget]; exact min_eq_right htop
      rw [this]; exact htopr.le)
    omega
  have hm₀pos : m₀ ≠ 0 := by
    intro h0
    rw [h0] at hm₀P
    have h0' : levelTarget δ' η₁ 0 = 25 * δ' := by
      simp only [levelTarget, pow_zero, mul_one]; exact min_eq_left h25
    rw [h0'] at hm₀P
    linarith
  have hprev : ¬ r ≤ levelTarget δ' η₁ (m₀ - 1) := Nat.find_min hP (by omega)
  push Not at hprev
  have hprev' : 25 * δ' * (δ' ^ (-(η₁ / 2))) ^ (m₀ - 1) < r := by
    rcases min_lt_iff.mp hprev with h | h
    · exact h
    · linarith
  refine ⟨⟨m₀, hm₀L⟩, (hm₀P.trans (hρlo ⟨m₀, hm₀L⟩)), ?_⟩
  have hhi := hρhi ⟨m₀, hm₀L⟩
  simp only at hhi
  have hlt : levelTarget δ' η₁ m₀ ≤ δ' ^ (-(η₁ / 2)) * (25 * δ' * (δ' ^ (-(η₁ / 2))) ^ (m₀ - 1)) := by
    refine (min_le_left _ _).trans (le_of_eq ?_)
    conv_lhs => rw [show m₀ = (m₀ - 1) + 1 by omega]
    ring
  calc lam * (25 * ρ ⟨m₀, hm₀L⟩) ≤ δ ^ (-η) * levelTarget δ' η₁ m₀ := hhi
    _ ≤ δ ^ (-η) * (δ' ^ (-(η₁ / 2)) * (25 * δ' * (δ' ^ (-(η₁ / 2))) ^ (m₀ - 1))) :=
        mul_le_mul_of_nonneg_left hlt hδη
    _ = (δ ^ (-η) * δ' ^ (-(η₁ / 2))) * (25 * δ' * (δ' ^ (-(η₁ / 2))) ^ (m₀ - 1)) := by ring
    _ ≤ δ' ^ (-η₁) * (25 * δ' * (δ' ^ (-(η₁ / 2))) ^ (m₀ - 1)) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
    _ ≤ δ' ^ (-η₁) * r := mul_le_mul_of_nonneg_left hprev'.le hδ'η.le

/-- Many tubes: a dense separated family has at least `δ ^ (η - 2) / 384` tubes. -/
theorem card_lower_of_separated {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hFam : Family η δ n x v Y) (hSep : Separated η δ n x v) :
    δ ^ η / (384 * δ ^ 2) ≤ (n : ℝ) := by
  obtain ⟨hn, hv, hball, -, -, -, -⟩ := hFam
  have hglob := hSep.global_frostman hδ hδ1 hn hball
  set i₀ : Fin n := ⟨0, hn⟩
  have hconv : Convex ℝ (tube δ (x i₀) (v i₀)) := (convex_segment _ _).thickening δ
  have h1 := hglob _ hconv
  have hone : (1 : ℝ) ≤ ({i | tube δ (x i) (v i) ⊆ tube δ (x i₀) (v i₀)}.ncard : ℝ) := by
    have : ({i₀} : Set (Fin n)) ⊆ {i | tube δ (x i) (v i) ⊆ tube δ (x i₀) (v i₀)} := by
      intro i hi
      rw [mem_singleton_iff] at hi
      rw [hi]
      show tube δ (x i₀) (v i₀) ⊆ tube δ (x i₀) (v i₀)
      exact Set.Subset.refl _
    have h2 := Set.ncard_le_ncard this
    rw [Set.ncard_singleton] at h2
    exact_mod_cast h2
  have hvol : volume (tube δ (x i₀) (v i₀)) ≤ ENNReal.ofReal (384 * δ ^ 2) := by
    have hseg : (fun t : ℝ => x i₀ + t • v i₀) '' Icc 0 1 = segment ℝ (x i₀) (x i₀ + v i₀) := by
      rw [segment_eq_image']; simp
    have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper (x i₀) (v i₀)
      (hv i₀) (T := Icc 0 1) subset_rfl hδ (A := 1) zero_le_one (by
        intro s hs t ht
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
    rw [hseg] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [sq_nonneg δ]
  have h3 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ) * (384 * δ ^ 2)) := by
    calc ENNReal.ofReal 1 ≤ ENNReal.ofReal
          ({i | tube δ (x i) (v i) ⊆ tube δ (x i₀) (v i₀)}.ncard : ℝ) := ENNReal.ofReal_le_ofReal hone
      _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume (tube δ (x i₀) (v i₀)) := h1
      _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * ENNReal.ofReal (384 * δ ^ 2) := by gcongr
      _ = ENNReal.ofReal (δ ^ (-η) * (n : ℝ) * (384 * δ ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  have hδη : δ ^ (-η) * δ ^ η = 1 := by rw [← Real.rpow_add hδ]; simp
  rw [div_le_iff₀ (by positivity)]
  have hpos : 0 < δ ^ η := Real.rpow_pos_of_pos hδ _
  calc δ ^ η = δ ^ η * 1 := by ring
    _ ≤ δ ^ η * (δ ^ (-η) * (n : ℝ) * (384 * δ ^ 2)) := mul_le_mul_of_nonneg_left h4 hpos.le
    _ = (δ ^ (-η) * δ ^ η) * ((n : ℝ) * (384 * δ ^ 2)) := by ring
    _ = (n : ℝ) * (384 * δ ^ 2) := by rw [hδη, one_mul]

theorem norm_alg_loss {a d2 lam P L1 N : ℝ} (hlam : 0 < lam) (hP : 0 < P) (hL1 : 0 < L1) :
    384 * d2 / lam * (a * a / (2 * 10 ^ 14 * lam ^ 2 * P * L1)) * (L1 * N) =
      (384 / (2 * 10 ^ 14)) * (a * a * d2 * N / (lam ^ 3 * P)) := by
  field_simp

theorem norm_alg_gain {a d2 lam P N : ℝ} (hlam : 0 < lam) (hP : 0 < P) :
    a * d2 / (13720 * lam) * (a * N / (7200000 * lam ^ 2) / 2) / (2 * P) =
      (1 / (13720 * 14400000 * 2)) * (a * a * d2 * N / (lam ^ 3 * P)) := by
  field_simp
  ring

theorem norm_alg_kappa {a d2 lam N : ℝ} (hlam : 0 < lam) (hN : 0 < N) :
    a * N * d2 / (4 * (3430 * lam * N)) = a * d2 / (13720 * lam) := by
  field_simp
  ring

theorem norm_alg_half {k C P : ℝ} (hP : 0 < P) : k * C / P = 2 * (k * C / (2 * P)) := by
  field_simp

theorem norm_alg_dense {a δ lam P C : ℝ} (hlam : 0 < lam) (hP : 0 < P) :
    lam ^ 3 * (a * δ ^ 2 / (13720 * lam) * C / (2 * P)) =
      C * (lam * δ) ^ 2 * (a / (27440 * P)) := by
  field_simp
  ring

theorem norm_alg_loss_le {a d2 lam P L1 N : ℝ} (hlam : 0 < lam) (hP : 0 < P) (hL1 : 0 < L1)
    (ha : 0 ≤ a) (hd2 : 0 ≤ d2) (hN : 0 ≤ N) :
    384 * d2 / lam * (a * a / (2 * 10 ^ 14 * lam ^ 2 * P * L1)) * (L1 * N) ≤
      a * d2 / (13720 * lam) * (a * N / (7200000 * lam ^ 2) / 2) / (2 * P) := by
  rw [norm_alg_loss hlam hP hL1, norm_alg_gain hlam hP]
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
