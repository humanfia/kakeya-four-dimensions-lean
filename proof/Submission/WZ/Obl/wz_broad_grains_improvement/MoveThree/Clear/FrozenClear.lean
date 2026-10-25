-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.FrozenClear.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/FrozenClear.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.EndpointStage
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.Length

/-!
# Endpoint clearance for the frozen stages of o153

The endpoint trimming of the ported o169 chain, generalized to an arbitrary end length
`ℓ`, and the short-length bound and endpoint clearance stated for this desk's frozen
stage predicate `J` (no thinness parameter). Requested by x0686 for the enlarged crossed
prisms of the per-fibre route.

`stage_length_small_frozen` and `endpoint_clear_J_frozen` are adapted from o169's
`stage_length_small` (`WangZahlLot/Obl/wz_move_three_wide_grains_core/ShortLength.lean`) and
`endpoint_clear_J` (`.../ClearStage.lean`), branch x0641 of the o169 repository (workspace
code, not accepted): `J` without the thinness field, and the end length `Kc * c`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

open MeasureTheory Set
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber fiberBodyCount fiberBodyCount_eq_ncard supported_fine_count
    assignedFiber_eq_supported assignedFiber_mono assignedFiber_common_cut fiberBodyCount_restrict)
open WangZahlLot.Obl.wz_coarse_tube_grains.RIS (tubeEnds)

/-- Endpoint clearance at an arbitrary end length `ℓ` (generalizing the o169 lemma,
which trims at the grain length): the full stage is trimmed away from the end
portions `tubeEnds δ ℓ` of all fine tubes, retaining a quarter of the fine mass and
preserving the given grain boxes. -/
theorem endpoint_clear_stage_data_len {ω ζ δ h ε ρ a c b g ℓ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hhε : h ≤ ε)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hH : H δ h n x v S Z ρ N y w f a c b g)
    (hδℓ : δ ≤ ℓ) (hℓ : ℓ ≤ 1 / 2) (hendbudget : 5120 * ℓ ≤ δ ^ (2 * h))
    (hmassbudget : δ ^ ε ≤ (1 / 8) * δ ^ h)
    (hbrbudget : 2 * δ ^ (-h) ≤ δ ^ (-ε)) :
    ∃ W : Fin n → Set V,
      (∀ i, W i ⊆ Z i ∧ Disjoint (W i) (tubeEnds δ ℓ (x i) (v i))) ∧
      O (1 / 4) * ∑ i, μ (Z i) ≤ ∑ i, μ (W i) ∧
      C δ ε n x v Y S W ρ N y w f True ∧
      Broad ω ζ δ ε ρ n N v S W f ∧
      H δ ε n x v S W ρ N y w f a c b g := by
  obtain ⟨L, z, e, Hs, γ, m, hHB⟩ := H_iff.mp hH
  have hsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hC.1 i).1
  have hdense : O (δ ^ (2 * h) * n * δ ^ 2) ≤ ∑ i, μ (Z i) := by
    calc
      O (δ ^ (2 * h) * n * δ ^ 2) = O (δ ^ h) * O (δ ^ h * n * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show 2 * h = h + h by ring, Real.rpow_add hδ]
        ring
      _ ≤ O (δ ^ h) * ∑ i, μ (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := hC.2.1.trans_eq (sum_supported hsupport)
  have hfin : (∑ i, μ (Z i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ =>
    ne_top_of_le_ne_top (measure_ball_lt_top (μ := volume) (x := (0 : V)) (r := 1)).ne
      (measure_mono ((hC.1 i).2.1.trans ((hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1)))
  have hlevelZ : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
    intro k p hp
    rw [assignedFiber_eq_supported f hsupport] at hp
    rw [← supported_fine_count f hsupport]
    exact hHB.2.2.2.2.2.2.2.2.1 k p hp
  have hm : 0 < m := by
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
    have hZpos : 0 < ∑ i, μ (Z i) := (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hdense
    obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
      (f := fun _ => (0 : ENNReal)) (g := fun i => μ (Z i)) (by simpa using hZpos)
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hi.ne'
    have hh := (hlevelZ (f i) p ⟨i, rfl, hp⟩).2
    have hpos : 0 < fiberBodyCount f Z (f i) p := by
      rw [fiberBodyCount_eq_ncard]
      exact Nat.cast_pos.mpr ((Set.ncard_pos (Set.toFinite _)).mpr ⟨i, rfl, hp⟩)
    linarith
  obtain ⟨U, hU, hmassU, hfracU⟩ := trim_fibre_endpoints x v Z f hδ hδℓ hℓ
    (fun i => (hA.2.1 i).1) hZm hfin hdense hendbudget
  have hUoff : ∀ i, i ∉ S → U i = ∅ := fun i hi =>
    subset_empty_iff.mp ((hU i).2.1.trans (by rw [hsupport i hi]))
  have hlevelU : ∀ k p, p ∈ assignedFiber f U k →
      m / 2 ≤ fiberBodyCount f U k p ∧ fiberBodyCount f U k p ≤ 2 * m := by
    intro k p hp
    have hz := hlevelZ k p (assignedFiber_mono f (fun i => (hU i).2.1) k hp)
    have hfrac : fiberBodyCount f Z k p ≤ 2 * fiberBodyCount f U k p := by
      simpa only [fiberBodyCount_eq_ncard, q] using hfracU k p hp
    have hle : fiberBodyCount f U k p ≤ fiberBodyCount f Z k p := by
      rw [fiberBodyCount_eq_ncard, fiberBodyCount_eq_ncard]
      exact Nat.cast_le.mpr (Set.ncard_mono fun i hi => ⟨hi.1, (hU i).2.1 hi.2⟩)
    constructor <;> linarith
  obtain ⟨m', D, hm', hm'm, hD, hmassD, hlevelD⟩ :=
    two_level_fibre_cut f U hm (fun i => (hU i).1) hlevelU
  let W i := U i ∩ D (f i)
  have hWm i : MeasurableSet (W i) := (hU i).1.inter (hD (f i))
  have hWZ i : W i ⊆ Z i := inter_subset_left.trans (hU i).2.1
  have hWoff : ∀ i, i ∉ S → W i = ∅ := fun i hi =>
    subset_empty_iff.mp ((hWZ i).trans (by rw [hsupport i hi]))
  have hmassW : O (1 / 4) * ∑ i, μ (Z i) ≤ ∑ i, μ (W i) := by
    calc
      O (1 / 4) * ∑ i, μ (Z i) = O (1 / 2) * (O (1 / 2) * ∑ i, μ (Z i)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ O (1 / 2) * ∑ i, μ (U i) := mul_le_mul' le_rfl hmassU
      _ ≤ _ := hmassD
  have hfracW : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ≤
        2 * q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} := by
    intro k p hp
    have hpW : p ∈ assignedFiber f W k := (assignedFiber_eq_supported f hWoff k).symm ▸ hp
    have hp' : p ∈ assignedFiber f U k ∩ D k := by
      change p ∈ assignedFiber f (fun i => U i ∩ D (f i)) k at hpW
      rwa [assignedFiber_common_cut] at hpW
    rw [show q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} = fiberBodyCount f Z k p from
      supported_fine_count f hsupport k p,
      show q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} = fiberBodyCount f W k p from
      supported_fine_count f hWoff k p]
    change fiberBodyCount f Z k p ≤ 2 * fiberBodyCount f (fun i => U i ∩ D (f i)) k p
    rw [fiberBodyCount_restrict, indicator_of_mem hp'.2]
    simpa only [fiberBodyCount_eq_ncard, q] using hfracU k p hp'.1
  have hlevelW : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} ∈ Icc m' (2 * m') := by
    intro k p hp
    rw [show q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} = fiberBodyCount f W k p from
      supported_fine_count f hWoff k p]
    exact hlevelD k p ((assignedFiber_eq_supported f hWoff k).symm ▸ hp)
  refine ⟨W, fun i => ⟨hWZ i, (hU i).2.2.mono_left inter_subset_left⟩, hmassW, ?_⟩
  exact shading_refine_stage_data hδ hδ1 hρ hhε hm (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hC hbr hHB hWm hWZ hmassW (by convert hmassbudget using 1 <;> norm_num)
    hfracW hbrbudget hlevelW

/-- Every admissible frozen stage has polynomially short grains, once its error is
small enough (o169's `stage_length_small`, for this desk's `J`). -/
theorem stage_length_small_frozen {ω ζ : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000) :
    ∃ h₀ d₀ : ℝ, 0 < h₀ ∧ 0 < d₀ ∧ ∀ δ h : ℝ,
      0 < δ → δ ≤ d₀ → h ≤ h₀ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
        ∀ ρ c j, J ω ζ δ h ρ c n x v Y j →
          c ≤ δ ^ (ω ^ 2 * ζ / 40000) ∧ c ≤ 1 / 4 := by
  let s : ℝ := ω ^ 2 * ζ / 10000
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := by
    have hw2 : ω ^ 2 ≤ 1 := by nlinarith
    have hz1 : ζ ≤ 1 / 1000 := by linarith
    have : ω ^ 2 * ζ ≤ 1 / 1000 :=
      (mul_le_mul_of_nonneg_right hw2 hζ.le).trans (by simpa using hz1)
    dsimp [s]
    linarith
  obtain ⟨d₁, hd₁, H₁⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (p := s / 4) (by positivity) (K := 1 / 2985984) (by norm_num)
  obtain ⟨d₂, hd₂, H₂⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (p := 1 - s / 4) (by linarith) (K := 1 / 4) (by norm_num)
  obtain ⟨d₃, hd₃, H₃⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (p := s / 4) (by positivity) (K := 1 / 4) (by norm_num)
  refine ⟨s / 12, min 1 (min d₁ (min d₂ d₃)), by positivity,
    lt_min one_pos (lt_min hd₁ (lt_min hd₂ hd₃)), ?_⟩
  intro δ h hδ hδd hh n x v Y hA ρ c j hJ
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hδd₁ : δ ≤ d₁ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₂ : δ ≤ d₂ := hδd.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₃ : δ ≤ d₃ := hδd.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρlower, _, hbr, hH, _⟩ := hJ
  have hc : c ≤ δ ^ (s / 4) := by
    by_cases h4 : 4 * δ ≤ c
    · have hδρ : δ ≤ ρ := by
        apply le_trans ?_ hρlower
        conv_lhs => rw [← Real.rpow_one δ]
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      have hρ : 0 < ρ := hδ.trans_le hδρ
      have hratio : δ / ρ ≤ δ ^ (ω / 100) := by
        apply (div_le_iff₀ hρ).mpr
        calc δ = δ ^ (ω / 100) * δ ^ (1 - ω / 100) := by
              rw [← Real.rpow_add hδ]
              convert (Real.rpow_one δ).symm using 2 <;> ring
          _ ≤ δ ^ (ω / 100) * ρ := mul_le_mul_of_nonneg_left hρlower (by positivity)
      have hβ : 0 ≤ ω * ζ / 100 := by positivity
      have hp : (δ / ρ) ^ (ω * ζ / 100) ≤ δ ^ s := by
        calc (δ / ρ) ^ (ω * ζ / 100) ≤ (δ ^ (ω / 100)) ^ (ω * ζ / 100) :=
              Real.rpow_le_rpow (by positivity) hratio hβ
          _ = δ ^ s := by rw [← Real.rpow_mul hδ.le]; congr 1; dsimp [s]; ring
      have hlen := broad_grains_length_bound hδ hδρ hA hC hbr hH h4
      have hlen' : c ^ 2 ≤ δ ^ (s / 2) := by
        calc c ^ 2 ≤ 2985984 * δ ^ (-(3 * h)) * (δ / ρ) ^ (ω * ζ / 100) := hlen
          _ ≤ 2985984 * δ ^ (-(3 * h)) * δ ^ s := by gcongr
          _ = 2985984 * δ ^ (s - 3 * h) := by rw [mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
          _ ≤ 2985984 * δ ^ (3 * s / 4) := by
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (by norm_num)
          _ = (2985984 * δ ^ (s / 4)) * δ ^ (s / 2) := by
              rw [mul_assoc, ← Real.rpow_add hδ]
              congr 2
              ring
          _ ≤ 1 * δ ^ (s / 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [H₁ δ hδ hδd₁]
          _ = _ := one_mul _
      have hp2 : (δ ^ (s / 4)) ^ 2 = δ ^ (s / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
        congr 1
        norm_num
        ring
      have hpos : 0 ≤ δ ^ (s / 4) := by positivity
      rw [← hp2] at hlen'
      nlinarith
    · have hsmall := H₂ δ hδ hδd₂
      have hδeq : δ = δ ^ (1 - s / 4) * δ ^ (s / 4) := by
        rw [← Real.rpow_add hδ, sub_add_cancel, Real.rpow_one]
      have hδle : δ ≤ (1 / 4) * δ ^ (s / 4) := by
        calc δ = δ ^ (1 - s / 4) * δ ^ (s / 4) := hδeq
          _ ≤ (1 / 4) * δ ^ (s / 4) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      linarith
  have he : s / 4 = ω ^ 2 * ζ / 40000 := by dsimp [s]; ring
  exact ⟨by simpa only [he] using hc, hc.trans (H₃ δ hδ hδd₃)⟩

/-- A frozen stage with its witnesses exposed and all fine shadings away from the end
portions of length `2 Kc c` of their tubes. -/
def ClearJF (ω ζ δ h ρ c Kc : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (j : ℕ) :
    Prop :=
  ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V)
    (f : Fin n → Fin N) (a g : ℝ),
    (∀ i, Disjoint (Z i) (tubeEnds δ (Kc * c) (x i) (v i))) ∧
    C δ h n x v Y S Z ρ N y w f True ∧ δ ^ (1 - ω / 100) ≤ ρ ∧ 0 < g ∧
    Broad ω ζ δ h ρ n N v S Z f ∧ H δ h n x v S Z ρ N y w f a c 0 g ∧
    ((1 ≤ j → δ ^ ζ * (ρ / δ) * N / n ≤ c) ∧
      (2 ≤ j → ρ ≤ δ ^ (ω / 100)) ∧ (3 ≤ j → g ≤ δ ^ (-ζ)))

theorem ClearJF.to_J {ω ζ δ h ρ c Kc : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {j : ℕ} (hclear : ClearJF ω ζ δ h ρ c Kc n x v Y j) :
    J ω ζ δ h ρ c n x v Y j := by
  obtain ⟨S, Z, N, y, w, f, a, g, _, hrest⟩ := hclear
  exact ⟨S, Z, N, y, w, f, a, g, hrest⟩

/-- Endpoint clearance with the witnesses of a frozen stage kept explicit: at any
requested error `ε` and any end length `Kc * c` (`1 ≤ Kc`), for all sufficiently small
`h, δ`, the fine shadings `Z` are cut to `W ⊆ Z` away from `tubeEnds δ (Kc * c)`,
keeping a quarter of their mass, the same `S, N, y, w, f, a, ρ, c, g`, and the stage
clauses at error `ε`; the grains are also short, `c ≤ δ ^ (ω ^ 2 * ζ / 40000)`. -/
theorem endpoint_clear_witnesses_frozen {ω ζ : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000) {ε Kc : ℝ} (hε : 0 < ε) (hK : 1 ≤ Kc) :
    ∃ h₀ d₀ : ℝ, 0 < h₀ ∧ h₀ ≤ ε ∧ 0 < d₀ ∧ ∀ δ h : ℝ,
      0 < δ → δ ≤ d₀ → h ≤ h₀ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
        ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V)
          (f : Fin n → Fin N) (a ρ c g : ℝ),
          C δ h n x v Y S Z ρ N y w f True → δ ^ (1 - ω / 100) ≤ ρ → 0 < g →
          Broad ω ζ δ h ρ n N v S Z f → H δ h n x v S Z ρ N y w f a c 0 g →
          ∃ W : Fin n → Set V,
            (∀ i, W i ⊆ Z i ∧ Disjoint (W i) (tubeEnds δ (Kc * c) (x i) (v i))) ∧
            O (1 / 4) * ∑ i, μ (Z i) ≤ ∑ i, μ (W i) ∧
            C δ ε n x v Y S W ρ N y w f True ∧
            Broad ω ζ δ ε ρ n N v S W f ∧
            H δ ε n x v S W ρ N y w f a c 0 g ∧
            c ≤ δ ^ (ω ^ 2 * ζ / 40000) := by
  let s : ℝ := ω ^ 2 * ζ / 40000
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨hL, dL, hhL, hdL, Hlen⟩ := stage_length_small_frozen hω hω1 hζ hζω
  obtain ⟨d₁, hd₁, H₁⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (p := s / 2) (by positivity) (K := 1 / (5120 * Kc)) (by positivity)
  obtain ⟨d₂, hd₂, H₂⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (p := ε / 2) (by positivity) (K := 1 / 8) (by norm_num)
  refine ⟨min hL (min (s / 4) (ε / 2)), min 1 (min dL (min d₁ d₂)),
    lt_min hhL (lt_min (by positivity) (by positivity)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith)),
    lt_min one_pos (lt_min hdL (lt_min hd₁ hd₂)), ?_⟩
  intro δ h hδ hδd hh n x v Y hA S Z N y w f a ρ c g hC hρlow hg hbr hH
  have hJ : J ω ζ δ h ρ c n x v Y 0 := ⟨S, Z, N, y, w, f, a, g, hC, hρlow, hg, hbr, hH,
    fun h1 => absurd h1 (by norm_num), fun h2 => absurd h2 (by norm_num),
    fun h3 => absurd h3 (by norm_num)⟩
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hδL : δ ≤ dL := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₁ : δ ≤ d₁ := hδd.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₂ : δ ≤ d₂ := hδd.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hhL' : h ≤ hL := hh.trans (min_le_left _ _)
  have hhs : h ≤ s / 4 := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhε : h ≤ ε / 2 := hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hcsmall, -⟩ := Hlen δ h hδ hδL hhL' n x v Y hA ρ c 0 hJ
  have hKpos : 0 < Kc := by linarith
  have hH1 := H₁ δ hδ hδd₁
  have hKs : 5120 * Kc * δ ^ (s / 2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hH1 (by positivity : (0 : ℝ) ≤ 5120 * Kc)
    rwa [mul_one_div_cancel (by positivity)] at this
  have hend : 5120 * (Kc * c) ≤ δ ^ (2 * h) := by
    calc 5120 * (Kc * c) ≤ 5120 * Kc * δ ^ s := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hcsmall (by positivity)
      _ = (5120 * Kc * δ ^ (s / 2)) * δ ^ (s / 2) := by
        rw [mul_assoc (5120 * Kc), ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ 1 * δ ^ (s / 2) := mul_le_mul_of_nonneg_right hKs (by positivity)
      _ ≤ δ ^ (2 * h) := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hratio : δ ^ (ε - h) ≤ 1 / 8 :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : ε / 2 ≤ ε - h)).trans
      (H₂ δ hδ hδd₂)
  have hmass : δ ^ ε ≤ (1 / 8) * δ ^ h := by
    calc δ ^ ε = δ ^ (ε - h) * δ ^ h := by rw [← Real.rpow_add hδ, sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)
  have hbrbudget : 2 * δ ^ (-h) ≤ δ ^ (-ε) := by
    calc
      2 * δ ^ (-h) = (2 * δ ^ (ε - h)) * δ ^ (-ε) := by
        rw [mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ 1 * δ ^ (-ε) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := one_mul _
  have hρ : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans_le hρlow
  obtain ⟨L₀, z₀, e₀, Hs₀, γ₀, m₀, hHB₀⟩ := H_iff.mp hH
  have hδc : δ ≤ c := hHB₀.1.trans (hHB₀.2.1.trans hHB₀.2.2.1)
  have hδℓ : δ ≤ Kc * c := hδc.trans (le_mul_of_one_le_left (hδ.le.trans hδc) hK)
  have hℓ : Kc * c ≤ 1 / 2 := by
    have hss : δ ^ s ≤ δ ^ (s / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h5 : 5120 * Kc * c ≤ 5120 * Kc * δ ^ (s / 2) :=
      mul_le_mul_of_nonneg_left (hcsmall.trans hss) (by positivity)
    nlinarith
  obtain ⟨W, hW, hmassW, hC', hbr', hH'⟩ := endpoint_clear_stage_data_len hδ hδ1 hρ
    (show h ≤ ε by linarith) hA hC hbr hH hδℓ hℓ hend hmass hbrbudget
  exact ⟨W, hW, hmassW, hC', hbr', hH', hcsmall⟩

/-- Endpoint clearance for every frozen stage, at any requested positive error and any
fixed end length `Kc * c` (`1 ≤ Kc`), uniformly at sufficiently small scales. -/
theorem endpoint_clear_J_frozen {ω ζ : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000) {ε Kc : ℝ} (hε : 0 < ε) (hK : 1 ≤ Kc) :
    ∃ h₀ d₀ : ℝ, 0 < h₀ ∧ h₀ ≤ ε ∧ 0 < d₀ ∧ ∀ δ h : ℝ,
      0 < δ → δ ≤ d₀ → h ≤ h₀ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
        ∀ ρ c j, J ω ζ δ h ρ c n x v Y j →
          ClearJF ω ζ δ ε ρ c Kc n x v Y j := by
  obtain ⟨h₀, d₀, hh₀, hh₀ε, hd₀, Hc⟩ := endpoint_clear_witnesses_frozen hω hω1 hζ hζω hε hK
  refine ⟨h₀, d₀, hh₀, hh₀ε, hd₀, ?_⟩
  intro δ h hδ hδd hh n x v Y hA ρ c j hJ
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρlow, hg, hbr, hH, hstops⟩ := hJ
  obtain ⟨W, hW, -, hC', hbr', hH', -⟩ :=
    Hc δ h hδ hδd hh n x v Y hA S Z N y w f a ρ c g hC hρlow hg hbr hH
  exact ⟨S, W, N, y, w, f, a, g, (fun i => (hW i).2), hC', hρlow, hg,
    hbr', hH', hstops⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
