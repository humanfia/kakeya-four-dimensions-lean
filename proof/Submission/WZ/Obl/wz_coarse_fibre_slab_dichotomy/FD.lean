-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.FD.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.Core
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.Numeric

/-!
# The fibre slab dichotomy with its parameters

`fd_main`: for `0 < c < τ` and `h > 0` there are `η₀, d₀` such that every admissible family
with a coarse cover (only the clauses actually needed are assumed) either has a refinement
satisfying the below-slab Frostman count with constant `δ^(-τ)` and mass `δ^τ`, or contains flat
non-interacting clusters (slabs of half-width `≤ δ^c ρ`) carrying mass `δ^h`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

open MeasureTheory Set Metric
open scoped ENNReal

local notation "Sp" => LeanEval.Analysis.WangZahlKakeya.Space

lemma volume_ball_one_le : volume (ball (0 : Sp) 1) ≤ ENNReal.ofReal 8 := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [Real.pi_lt_four]

lemma doubled_eq (ρ : ℝ) (y w : Sp) :
    thickening (2 * ρ) (segment ℝ (y - (1 / 2 : ℝ) • w) (y - (1 / 2 : ℝ) • w + 2 • w)) =
      doubled ρ y w := by
  simp only [doubled, two_smul]

/-- A set-builder count over a finset filter. -/
lemma ncard_filter_eq {n : ℕ} (S : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P] :
    ({i | i ∈ S ∧ P i} : Set (Fin n)).ncard = (S.filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

/-- The scalar mass bookkeeping of the flat-cluster alternative. -/
lemma fd_mass_real {a yr zS P M L θ n δ δh δτ : ℝ} (ha0 : 0 < a) (hyr0 : 0 ≤ yr)
    (hL1 : 1 ≤ L) (hn0 : 0 ≤ n) (hY1 : a * n * δ ^ 2 ≤ yr) (hZS : a * yr ≤ zS)
    (hθa : θ = a ^ 2 / 6144)
    (hmass : zS ≤ 3072 * θ * n * δ ^ 2 + 2 * L / θ ^ 2 * (P + 2 * M))
    (hM : M = δτ * yr) (hnum : 4 * 6144 ^ 2 * L * (δh + 2 * δτ) ≤ a ^ 5) :
    δh * yr ≤ P := by
  have hfirst : 3072 * θ * n * δ ^ 2 ≤ zS / 2 := by
    rw [hθa]
    have : 3072 * (a ^ 2 / 6144) * n * δ ^ 2 = a / 2 * (a * n * δ ^ 2) := by ring
    rw [this]
    have e1 : a / 2 * (a * n * δ ^ 2) ≤ a / 2 * yr :=
      mul_le_mul_of_nonneg_left hY1 (by positivity)
    linarith
  have ha4 : 0 < a ^ 4 := by positivity
  have hθ2 : θ ^ 2 = a ^ 4 / 6144 ^ 2 := by rw [hθa]; ring
  have e1 : a * yr ≤ (4 * 6144 ^ 2 * L * (P + 2 * M)) / a ^ 4 := by
    have h1 : 2 * L / θ ^ 2 * (P + 2 * M) = (2 * 6144 ^ 2 * L * (P + 2 * M)) / a ^ 4 := by
      rw [hθ2]; field_simp
    have h2 : (4 * 6144 ^ 2 * L * (P + 2 * M)) / a ^ 4 =
        2 * ((2 * 6144 ^ 2 * L * (P + 2 * M)) / a ^ 4) := by ring
    rw [h1] at hmass
    rw [h2]
    linarith
  rw [le_div_iff₀ ha4] at e1
  have hkey : a ^ 5 * yr ≤ 4 * 6144 ^ 2 * L * (P + 2 * M) := by
    have : a ^ 5 * yr = a * yr * a ^ 4 := by ring
    linarith
  have hC0 : 0 < 4 * 6144 ^ 2 * L := by positivity
  have e3 : 4 * 6144 ^ 2 * L * ((δh + 2 * δτ) * yr) ≤ 4 * 6144 ^ 2 * L * (P + 2 * M) := by
    calc 4 * 6144 ^ 2 * L * ((δh + 2 * δτ) * yr)
        = (4 * 6144 ^ 2 * L * (δh + 2 * δτ)) * yr := by ring
      _ ≤ a ^ 5 * yr := mul_le_mul_of_nonneg_right hnum hyr0
      _ ≤ _ := hkey
  have e4 := le_of_mul_le_mul_left e3 hC0
  rw [hM] at e4
  linarith

open Classical in
theorem fd_main {τ c h : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hcτ : c < τ) (hh : 0 < h) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ (n : ℕ) (x v : Fin n → Sp) (Y : Fin n → Set Sp),
        (∀ i, ‖v i‖ = 1 ∧ thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Sp) 1 ∧
          MeasurableSet (Y i) ∧ Y i ⊆ thickening δ (segment ℝ (x i) (x i + v i))) →
        ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤ ∑ i, volume (Y i) →
        (∀ W : Set Sp, Convex ℝ W →
          ENNReal.ofReal ((({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} :
            Set (Fin n)).ncard : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * volume W) →
      ∀ (ρ : ℝ) (S : Finset (Fin n)) (Z : Fin n → Set Sp) (N : ℕ) (y w : Fin N → Sp)
        (f : Fin n → Fin N),
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) →
        ENNReal.ofReal (δ ^ η) * ∑ i, volume (Y i) ≤ ∑ i ∈ S, volume (Z i) →
        (∀ k, ‖w k‖ = 1) →
        (∀ i ∈ S, thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          thickening ρ (segment ℝ (y (f i)) (y (f i) + w (f i)))) →
        δ ≤ ρ → ρ ≤ 1 →
        (∃ (S' : Finset (Fin n)) (Z' : Fin n → Set Sp), S' ⊆ S ∧
          (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i ∧ (i ∉ S' → Z' i = ∅)) ∧
          ENNReal.ofReal (δ ^ τ) * ∑ i, volume (Y i) ≤ ∑ i ∈ S', volume (Z' i) ∧
          ∀ (k : Fin N) (u : Sp) (t r : ℝ), ‖u‖ = 1 → 0 < r →
            ENNReal.ofReal ((({i | i ∈ S' ∧ f i = k ∧
                thickening δ (segment ℝ (x i) (x i + v i)) ⊆
                  thickening (2 * ρ) (segment ℝ (y k - (1 / 2 : ℝ) • w k)
                    (y k - (1 / 2 : ℝ) • w k + 2 • w k)) ∩ {p | |inner ℝ u p - t| ≤ r}} :
                Set (Fin n)).ncard : ℝ)) *
              volume (thickening (2 * ρ) (segment ℝ (y k - (1 / 2 : ℝ) • w k)
                (y k - (1 / 2 : ℝ) • w k + 2 • w k))) ≤
            ENNReal.ofReal (δ ^ (-τ) * (({i | i ∈ S' ∧ f i = k} : Set (Fin n)).ncard : ℝ)) *
              volume (thickening (2 * ρ) (segment ℝ (y k - (1 / 2 : ℝ) • w k)
                (y k - (1 / 2 : ℝ) • w k + 2 • w k)) ∩ {p | |inner ℝ u p - t| ≤ r})) ∨
        (∃ (G : Finset (Fin n)) (Z₁ : Fin n → Set Sp) (u : Fin n → Sp) (t r : Fin n → ℝ),
          G ⊆ S ∧ (∀ i, MeasurableSet (Z₁ i) ∧ Z₁ i ⊆ Z i ∧ (i ∉ G → Z₁ i = ∅)) ∧
          ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i ∈ G, volume (Z₁ i) ∧
          (∀ i ∈ G, ‖u i‖ = 1 ∧ 0 < r i ∧ r i ≤ δ ^ c * ρ ∧
            thickening δ (segment ℝ (x i) (x i + v i)) ⊆ {p | |inner ℝ (u i) p - t i| ≤ r i}) ∧
          (∀ i ∈ G, ∀ j ∈ G, f i = f j → (Z₁ i ∩ Z₁ j).Nonempty →
            thickening δ (segment ℝ (x j) (x j + v j)) ⊆
              {p | |inner ℝ (u i) p - t i| ≤ r i})) := by
  obtain ⟨η₀, d₀, hη₀, hη₀', hd₀, hd₀', hnum⟩ := fd_numeric hτ hc hcτ hh
  refine ⟨η₀, hη₀, d₀, hd₀, hd₀', ?_⟩
  intro δ hδ hδd η hη hηη₀ n x v Y hA hmassY hKT ρ S Z N y w f hZ hmassZ hw hcov hδρ hρ1
  have hδ1 : δ ≤ 1 / 100 := hδd.trans hd₀'
  have hδh : δ ≤ 1 / 2 := by linarith
  have hδ1' : δ ≤ 1 := by linarith
  have hρ0 : 0 < ρ := hδ.trans_le hδρ
  have hη1 : η ≤ 1 / 2 := hηη₀.trans hη₀'
  obtain ⟨hnum1, hnum2, hnum3⟩ := hnum δ η hδ hδd hη.le hηη₀
  have hv : ∀ i, ‖v i‖ = 1 := fun i => (hA i).1
  have hT : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Sp) 1 :=
    fun i => (hA i).2.1
  have hYT : ∀ i, Y i ⊆ thickening δ (segment ℝ (x i) (x i + v i)) := fun i => (hA i).2.2.2
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hZ i).1
  have hZT : ∀ i, Z i ⊆ thickening δ (segment ℝ (x i) (x i + v i)) :=
    fun i => (hZ i).2.1.trans (hYT i)
  have hYt : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (measure_ball_lt_top (x := (0 : Sp)) (r := 1)).ne
      (measure_mono ((hYT i).trans (hT i)))
  have hZt : ∀ i, volume (Z i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hYt i) (measure_mono (hZ i).2.1)
  set yr := ∑ i, (volume (Y i)).toReal with hyr
  have hyr0 : 0 ≤ yr := Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
  have hsumY : ∑ i, volume (Y i) = ENNReal.ofReal yr := by
    rw [hyr, ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_toReal (hYt i)).symm)
  have hsumZ : ∀ s : Finset (Fin n), ∑ i ∈ s, volume (Z i) =
      ENNReal.ofReal (∑ i ∈ s, (volume (Z i)).toReal) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_toReal (hZt i)).symm)
  -- powers of δ
  set a := δ ^ η with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hδ η
  have ha1 : a ≤ 1 := Real.rpow_le_one hδ.le hδ1' hη.le
  have h2η : δ ^ (2 * η) = a ^ 2 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; ring_nf
  have h5η : δ ^ (5 * η) = a ^ 5 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; ring_nf
  -- the number of tubes
  have hn : (n : ℝ) * δ ^ 2 ≤ 8 * δ ^ (-η) := by
    have h1 := hKT (ball 0 1) (convex_ball 0 1)
    have hall : ({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Sp) 1} :
        Set (Fin n)).ncard = n := by
      have hset : ({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Sp) 1} :
          Set (Fin n)) = Set.univ := Set.eq_univ_of_forall (fun i => hT i)
      rw [hset, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hall] at h1
    have h2 : ENNReal.ofReal ((n : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (8 * δ ^ (-η)) := by
      calc ENNReal.ofReal ((n : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * volume (ball (0 : Sp) 1) := h1
        _ ≤ ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal 8 := by gcongr; exact volume_ball_one_le
        _ = ENNReal.ofReal (8 * δ ^ (-η)) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hδ _).le]; ring_nf
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  have hn3 : (n : ℝ) ≤ 8 * δ ^ (-(3 : ℝ)) := by
    have e1 : δ ^ (-η) ≤ δ ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith)
    have e2 : δ ^ (-(3 : ℝ)) = δ ^ (-(1 : ℝ)) / δ ^ 2 := by
      rw [show (-(3 : ℝ)) = -(1 : ℝ) + -(2 : ℝ) by norm_num, Real.rpow_add hδ,
        Real.rpow_neg hδ.le 2, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [e2, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  -- the logarithmic parameter
  set K : ℕ := ⌈Real.logb 2 (12288 * δ ^ (-(3 : ℝ)))⌉₊ with hKdef
  have hX : 1 ≤ 12288 * δ ^ (-(3 : ℝ)) := by
    have : 1 ≤ δ ^ (-(3 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1' (by norm_num)
    linarith
  have hK : (1536 * n : ℝ) ≤ 2 ^ K := by
    calc (1536 * n : ℝ) ≤ 12288 * δ ^ (-(3 : ℝ)) := by linarith
      _ = (2 : ℝ) ^ Real.logb 2 (12288 * δ ^ (-(3 : ℝ))) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ (2 : ℝ) ^ (K : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ K := Real.rpow_natCast 2 K
  have hKle : (K : ℝ) ≤ (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2 + 1 := by
    have hlogb0 : 0 ≤ Real.logb 2 (12288 * δ ^ (-(3 : ℝ))) :=
      Real.logb_nonneg (by norm_num) hX
    have h1 := Nat.ceil_lt_add_one hlogb0
    have h2 : Real.logb 2 (12288 * δ ^ (-(3 : ℝ))) =
        (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2 := by
      rw [Real.logb, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hδ _).ne',
        Real.log_rpow hδ, one_div, Real.log_inv]
      ring
    rw [← hKdef] at h1
    linarith
  set L : ℝ := 1 + 320 * K with hL
  have hLle : L ≤ 321 + 320 * (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2 := by
    have e : 320 * (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2 =
        320 * ((Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2) := by ring
    rw [hL, e]; linarith
  have hL1 : 1 ≤ L := by rw [hL]; have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith
  -- apply the core dichotomy
  set θ := δ ^ (2 * η) / 6144 with hθdef
  have hθ : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθdef, h2η]; nlinarith
  set lam := δ ^ c * ρ with hlamdef
  have hlam : 0 < lam := by positivity
  set M := δ ^ τ * yr with hMdef
  have hM : 0 ≤ M := by positivity
  rcases core_dichotomy hδ hδh hρ0 hρ1 x v hv hT S Z hZm hZT y w hw f hcov hθ hθ1 K hK hlam hM
    with ⟨S', hS'S, hMle, hcount⟩ | ⟨S'', Z'', u, t, r, hS''S, hZ'', hmass, hslab, hnonint⟩
  · -- the refinement alternative
    left
    refine ⟨S', fun i => if i ∈ S' then Z i else ∅, hS'S, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with hi
      · exact ⟨hZm i, subset_rfl, fun h => absurd hi h⟩
      · exact ⟨MeasurableSet.empty, empty_subset _, fun _ => rfl⟩
    · have hsum' : ∑ i ∈ S', volume (if i ∈ S' then Z i else ∅) = ∑ i ∈ S', volume (Z i) :=
        Finset.sum_congr rfl (fun i hi => by simp only [hi, if_true])
      rw [hsum', hsumY, hsumZ, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hδ τ).le]
      exact ENNReal.ofReal_le_ofReal hMle
    · intro k u' t' r' hu' hr'
      have hcnt := hcount k u' t' r' hu' hr'
      simp only [slabQ] at hcnt
      rw [doubled_eq, ncard_filter_eq S' (fun i => f i = k ∧
          thickening δ (segment ℝ (x i) (x i + v i)) ⊆
            doubled ρ (y k) (w k) ∩ {p | |inner ℝ u' p - t'| ≤ r'}),
        ncard_filter_eq S' (fun i => f i = k)]
      have hl2 : 589824 * ρ / (lam * θ) = 589824 * 6144 * δ ^ (-(c + 2 * η)) := by
        rw [hlamdef, hθdef, Real.rpow_neg hδ.le, Real.rpow_add hδ]
        have h1 : 0 < δ ^ c := Real.rpow_pos_of_pos hδ c
        have h2 : 0 < δ ^ (2 * η) := Real.rpow_pos_of_pos hδ _
        field_simp
      have hl : max 384 (589824 * ρ / (lam * θ)) ≤ δ ^ (-τ) := by
        rw [hl2]; exact max_le hnum1 hnum2
      calc _ ≤ _ := hcnt
        _ ≤ _ := by gcongr
  · -- flat clusters
    right
    refine ⟨S'', Z'', u, t, r, hS''S, hZ'', ?_, ?_, ?_⟩
    · have hZ''t : ∀ i, volume (Z'' i) ≠ ⊤ := fun i =>
        ne_top_of_le_ne_top (hZt i) (measure_mono (hZ'' i).2.1)
      set P := ∑ i ∈ S'', (volume (Z'' i)).toReal with hP
      have hP0 : 0 ≤ P := Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
      have hsumZ'' : ∑ i ∈ S'', volume (Z'' i) = ENNReal.ofReal P := by
        rw [hP, ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
        exact Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_toReal (hZ''t i)).symm)
      rw [hsumY, hsumZ'', ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hδ h).le]
      apply ENNReal.ofReal_le_ofReal
      set zS := ∑ i ∈ S, (volume (Z i)).toReal with hzS
      have hY1 : a * n * δ ^ 2 ≤ yr := by
        have := hmassY
        rw [hsumY] at this
        exact (ENNReal.ofReal_le_ofReal_iff hyr0).mp this
      have hZS : a * yr ≤ zS := by
        have := hmassZ
        rw [hsumY, hsumZ, ← ENNReal.ofReal_mul ha0.le] at this
        exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg
          (fun i _ => ENNReal.toReal_nonneg))).mp this
      have hθa : θ = a ^ 2 / 6144 := by rw [hθdef, h2η]
      have hnum3' : 4 * 6144 ^ 2 * L * (δ ^ h + 2 * δ ^ τ) ≤ a ^ 5 := by
        rw [← h5η]
        calc 4 * 6144 ^ 2 * L * (δ ^ h + 2 * δ ^ τ)
            ≤ 4 * 6144 ^ 2 * (321 + 320 * (Real.log 12288 + 3 * Real.log (1 / δ)) /
              Real.log 2) * (δ ^ h + 2 * δ ^ τ) := by
              have hp : 0 ≤ δ ^ h + 2 * δ ^ τ := by positivity
              gcongr
          _ ≤ δ ^ (5 * η) := hnum3
      have hmass' := hmass
      rw [← hL] at hmass'
      exact fd_mass_real ha0 hyr0 hL1 (Nat.cast_nonneg n) hY1 hZS hθa hmass' hMdef hnum3'
    · intro i hi
      obtain ⟨h1, h2, h3, h4⟩ := hslab i hi
      exact ⟨h1, h2, h3.le, h4⟩
    · intro i hi j hj hf hne
      exact hnonint i hi j hj hf hne

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
