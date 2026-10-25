-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGStage
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Incidence

/-!
# Global grains from one rescaled fibre

Prop. 4.1 of the sticky Kakeya paper after the fibre rescaling: the slab stage, the rotation
stage, and a second application of the plane-grains transfer produce weak global and local
grains (`WeakGrains` of the split of o061).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical RealInnerProductSpace
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- The conclusion of the plane-grains transfer for one input family at scale `τ'`. -/
def PGTAt (σ c ε2 η2 τ' : ℝ) : Prop :=
  ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Family η2 τ' n x v Y → Separated η2 τ' n x v →
    volume (⋃ i, Y i) ≤ ENNReal.ofReal (τ' ^ (σ - η2)) →
    ∃ δ' : ℝ, τ' ^ c ≤ δ' ∧ δ' ≤ τ' ^ (c - ε2) ∧ δ' ≤ (1 / 100 : ℝ) ∧
      ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
        Family ε2 δ' m x' v' Y' ∧ Separated ε2 δ' m x' v' ∧
        volume (⋃ j, Y' j) ≤ ENNReal.ofReal (δ' ^ (σ - ε2)) ∧
        (⋃ j, Y' j) ⊆ thickening (10 * δ') (⋃ i, Y i) ∧
        ∃ V : Space → Space, (∀ p, p ∈ (⋃ j, Y' j) → ‖V p‖ = 1) ∧
          (∀ j p, p ∈ Y' j → |inner ℝ (v' j) (V p)| ≤ δ') ∧
          (∀ p q, p ∈ (⋃ j, Y' j) → q ∈ (⋃ j, Y' j) → dist (V p) (V q) ≤ δ' ^ (-ε2) * dist p q) ∧
          (∀ ρ : ℝ, δ' ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ j, Y' j) →
            Covering ρ (1 - σ) (δ' ^ (-ε2))
              ((fun q : Space => inner ℝ (V p) q) '' ((⋃ j, Y' j) ∩ ball p (Real.sqrt ρ))))

/-- The body of `WeakGrains σ` for one error and one cutoff. -/
def WeakGrainsAt (σ ε d0 : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family ε δ n x v Y ∧ Separated ε δ n x v ∧ volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) ∧
      ∃ (f : ℝ → ℝ) (V : Space → Space), (∀ z z' : ℝ, dist (f z) (f z') ≤ δ ^ (-ε) * dist z z') ∧
        (∀ z : ℝ, z ∈ Icc (-1) 1 → Covering δ (1 - σ) (δ ^ (-ε)) (projectedSlice f (⋃ i, Y i) z)) ∧
        (∀ p, p ∈ (⋃ i, Y i) → ‖V p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) ∧
        (∀ p q, p ∈ (⋃ i, Y i) → q ∈ (⋃ i, Y i) → dist (V p) (V q) ≤ δ ^ (-ε) * dist p q) ∧
        (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
          Covering ρ (1 - σ) (δ ^ (-ε))
            ((fun q : Space => inner ℝ (V p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))

/-- Global grains from one rescaled fibre: the slab stage, the rotation stage and the second
plane-grains transfer. -/
theorem gg_after_fibre {σ ε c ε2 η2 εF τ ρ0 b τ' L C d0 : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hε : 0 ≤ ε) (hε2ε : ε2 ≤ ε)
    (hτ : 0 < τ) (hτρ : τ ≤ ρ0) (hρ0 : ρ0 ≤ 1 / 100) (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hτ'0 : 0 < τ') (hτ'h : τ' ≤ b * ρ0) (hτ'1 : τ' ≤ 1)
    {E : Set Space} {V : Space → Space}
    (hV1 : ∀ p ∈ E, ‖V p‖ = 1)
    (hVL : ∀ p ∈ E, ∀ q ∈ E, dist (V p) (V q) ≤ L * dist p q)
    (hloc : ∀ p ∈ E, Covering ((5 * ρ0) ^ 2) (1 - σ) C
      ((fun q => ⟪V p, q⟫) '' (E ∩ ball p (5 * ρ0))))
    {z0 w0 : Space} (hw0 : ‖w0‖ = 1)
    {n : ℕ} {x v : Fin n → Space} {Y' : Fin n → Set Space} (hv : ∀ i, ‖v i‖ = 1)
    {m : ℕ} (ι : Fin m → Fin n)
    (hYE : ∀ q, Y' (ι q) ⊆ E) (hYT : ∀ q, Y' (ι q) ⊆ tube τ (x (ι q)) (v (ι q)))
    (hTlev : ∀ q, tube τ (x (ι q)) (v (ι q)) ⊆ tube ρ0 z0 w0)
    (hVv : ∀ q, ∀ p ∈ Y' (ι q), |⟪v (ι q), V p⟫| ≤ τ)
    (hFam : Family εF τ' m
      (fun q => resc w0 (z0 + (1 / 2 : ℝ) • w0) (1 / 100 / ρ0) b
        (orStart w0 (x (ι q)) (v (ι q))))
      (fun q => ndir w0 (1 / 100 / ρ0) (orDir w0 (v (ι q))))
      (fun q => resc w0 (z0 + (1 / 2 : ℝ) • w0) (1 / 100 / ρ0) b '' Y' (ι q)))
    (hSep : Separated εF τ' m
      (fun q => resc w0 (z0 + (1 / 2 : ℝ) • w0) (1 / 100 / ρ0) b
        (orStart w0 (x (ι q)) (v (ι q))))
      (fun q => ndir w0 (1 / 100 / ρ0) (orDir w0 (v (ι q)))))
    (hvolF : volume (⋃ q, resc w0 (z0 + (1 / 2 : ℝ) • w0) (1 / 100 / ρ0) b '' Y' (ι q)) ≤
      ENNReal.ofReal (τ' ^ (σ - εF)))
    (hPGT : PGTAt σ c ε2 η2 τ') (hεFη2 : εF ≤ η2)
    {N : ℕ} (hN : 1 ≤ N) (hNh : (N : ℝ) * (b * ρ0) ≤ 1)
    (hNL : 8 * L * (2 * (ρ0 * (N + 2)) + 6 * τ) ≤ 1 / 2)
    (hmassN : τ' ^ η2 ≤ (N : ℝ) * (b * ρ0) / 7 * (τ' ^ εF * τ' ^ εF / 11648))
    (hfin : ∀ δf : ℝ, τ' ^ c ≤ δf → δf ≤ τ' ^ (c - ε2) →
      b * ρ0 ≤ δf ^ (-(ε / 8)) * δf ∧ δf ≤ δf ^ (-(ε / 8)) * (b * ρ0) ∧
      1280 * L ≤ δf ^ (-(ε / 8)) ∧
      20800 * (δf ^ (-(ε / 8))) ^ 3 * (4 ^ (1 - σ) * C) ≤ δf ^ (-ε) ∧ δf ≤ d0 ∧
      1280 * L ≤ δf ^ (-ε)) :
    WeakGrainsAt σ ε d0 := by
  classical
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le hτ hτρ
  set φ := resc w0 (z0 + (1 / 2 : ℝ) • w0) (1 / 100 / ρ0) b with hφ
  obtain ⟨hm, hVd1, hball, hhalf, hYm, hYsub, hmassF⟩ := id hFam
  have hVhw : ∀ q, 1 / 2 ≤ |⟪ndir w0 (1 / 100 / ρ0) (orDir w0 (v (ι q))), w0⟫| := fun q =>
    inner_ndir_ge hτ hρ0pos hρ0 (hv (ι q)) hw0 (hTlev q)
  -- the slab stage
  obtain ⟨q0, k, Zb, Vhat, hmass, hcover, hVdirs, hLip, hblock⟩ :=
    slab_stage hτ hτρ hρ0 (by linarith) hb1 hσ1 hC hL hτ'0 hV1 hVL hloc hw0 hv ι hYE hYT hTlev
      hVv hFam hVhw hτ'h hN hNh
  set Y2 : Fin m → Set Space := fun q => φ '' Y' (ι q) ∩
    slabsOf w0 (b * ρ0) (φ '' Y' (ι q0)) ∩ slab w0 ((N : ℝ) * (b * ρ0)) k with hY2
  set U : Set Space := ⋃ q, Y2 q with hU
  have hY2sub : ∀ q, Y2 q ⊆ φ '' Y' (ι q) := fun q => inter_subset_left.trans inter_subset_left
  have hY2m : ∀ q, MeasurableSet (Y2 q) := fun q =>
    ((hYm q).inter (measurableSet_slabsOf _ _ _)).inter (measurableSet_slab _ _ _)
  have hUb : U ⊆ ball 0 1 := iUnion_subset fun q => (hY2sub q).trans ((hYsub q).trans (hball q))
  set G : Set Space := φ '' ⋃ q, Y' (ι q) with hG
  have hUG : U ⊆ G := by
    rw [hG, Set.image_iUnion]
    exact iUnion_mono hY2sub
  -- the restricted family keeps its mass
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmass2 : τ' ^ η2 * m * τ' ^ 2 ≤ shadingMass Y2 := by
    have h1 : τ' ^ η2 * m * τ' ^ 2 ≤
        (N : ℝ) * (b * ρ0) / 7 * (τ' ^ εF * τ' ^ εF * m * τ' ^ 2 / 11648) := by
      have := mul_le_mul_of_nonneg_right hmassN (by positivity : (0 : ℝ) ≤ m * τ' ^ 2)
      calc τ' ^ η2 * m * τ' ^ 2 = τ' ^ η2 * (m * τ' ^ 2) := by ring
        _ ≤ (N : ℝ) * (b * ρ0) / 7 * (τ' ^ εF * τ' ^ εF / 11648) * (m * τ' ^ 2) := this
        _ = _ := by ring
    exact h1.trans hmass
  have hZbne : Zb.Nonempty := by
    have hpos : 0 < shadingMass Y2 := lt_of_lt_of_le (by positivity) hmass2
    obtain ⟨q, -, hq⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
      (f := fun _ => (0 : ℝ)) (g := fun q => (volume (Y2 q)).toReal)
      (by simpa [shadingMass] using hpos)
    have hne : (Y2 q).Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      simp [hcon] at hq
    obtain ⟨p, hp⟩ := hne
    obtain ⟨z, hz, -⟩ := hcover q p hp
    exact ⟨z, hz⟩
  -- the rotation stage
  obtain ⟨R, f, hfL, hslices⟩ := rotate_stage (C := 4 ^ (1 - σ) * C) hτ hτρ hb hσ0 hσ1
    (by positivity) hL hw0 hUb hUG Zb hZbne Vhat
    (fun p hp => by
      obtain ⟨q, hq⟩ := mem_iUnion.mp hp
      exact hcover q p hq)
    hVdirs hLip hblock hNL
  -- the rotated restricted family
  have hFam2 : Family η2 τ' m
      (fun q => φ (orStart w0 (x (ι q)) (v (ι q))))
      (fun q => ndir w0 (1 / 100 / ρ0) (orDir w0 (v (ι q)))) Y2 :=
    hFam.of_subsets_mass hY2sub hY2m hmass2
  have hFam3 := hFam2.isometry R
  have hSep3 := (hSep.mono_error hτ'0 hτ'1 hεFη2).isometry R
  have hvol3 : volume (⋃ q, R '' Y2 q) ≤ ENNReal.ofReal (τ' ^ (σ - η2)) := by
    rw [← Set.image_iUnion, volume_image_isometry]
    calc volume (⋃ q, Y2 q) ≤ volume (⋃ q, φ '' Y' (ι q)) := measure_mono (iUnion_mono hY2sub)
      _ ≤ ENNReal.ofReal (τ' ^ (σ - εF)) := hvolF
      _ ≤ ENNReal.ofReal (τ' ^ (σ - η2)) := ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_ge hτ'0 hτ'1 (by linarith))
  -- the second plane-grains transfer
  obtain ⟨δf, hδlo, hδhi, hδ100, mf, xf, vf, Yf, hFf, hSf, hvolf, hnear, W, hW1, hWv, hWL, hWloc⟩ :=
    hPGT m _ _ _ hFam3 hSep3 hvol3
  have hδf : 0 < δf := lt_of_lt_of_le (Real.rpow_pos_of_pos hτ'0 c) hδlo
  have hδf1 : δf ≤ 1 := hδ100.trans (by norm_num)
  obtain ⟨hK1, hK2, hK3, hK4, hd0, hfLip⟩ := hfin δf hδlo hδhi
  have hKge : 1 ≤ δf ^ (-(ε / 8)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδf hδf1 (by linarith)
  have hεle : δf ^ (-ε2) ≤ δf ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by linarith)
  refine ⟨δf, hδf, hd0, hδ100, mf, xf, vf, Yf, hFf.mono_error hδf hδf1 hε2ε,
    hSf.mono_error hδf hδf1 hε2ε, hvolf.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by linarith))), f, W, ?_, ?_, hW1, hWv, ?_, ?_⟩
  · intro z z'
    rw [Real.dist_eq, Real.dist_eq]
    exact (hfL z z').trans (mul_le_mul_of_nonneg_right hfLip (abs_nonneg _))
  · intro z _
    have hnear' : (⋃ j, Yf j) ⊆ thickening (10 * δf) (R '' U) := by
      rw [hU, Set.image_iUnion]; exact hnear
    exact (hslices (⋃ j, Yf j) δf (δf ^ (-(ε / 8))) hδf (hδ100.trans (by norm_num)) hKge hK3 hK1
      hK2 hnear' z).mono_constant hδf hK4
  · intro p q hp hq
    exact (hWL p q hp hq).trans (mul_le_mul_of_nonneg_right hεle dist_nonneg)
  · intro ρ hρ1 hρ2 p hp
    exact (hWloc ρ hρ1 hρ2 p hp).mono_constant (lt_of_lt_of_le hδf hρ1) hεle

/-- The anisotropic shrinking factor of the fibre rescaling. -/
noncomputable def bR : ℝ := 1 / (1 + 144 * (1 / 100) ^ 2)

theorem bR_pos : 0 < bR := by rw [bR]; positivity
theorem half_le_bR : 1 / 2 ≤ bR := by rw [bR, le_div_iff₀ (by positivity)]; norm_num
theorem bR_le_one : bR ≤ 1 := by rw [bR, div_le_one (by positivity)]; norm_num

/-- The numerical conditions of the global grains at one level radius `ρ0`. -/
structure GGNum (σ ε c ε2 η2 εF εT ε1 tF τ ρc ρ0 d0 τ'max : ℝ) : Prop where
  hρc : ρc ≤ 1 / 1000
  hloc1 : τ ≤ (5 * ρ0) ^ 2
  hloc2 : (5 * ρ0) ^ 2 ≤ 1
  hsmall : bR * (1 / 100 / ρ0) * τ ≤ 1 / 10000000
  hC2a : 34 * τ ^ (-(2 * εT)) ≤ (bR * (1 / 100 / ρ0) * τ) ^ (-εF)
  hC2b : (bR * (1 / 100 / ρ0) * τ) ^ εF ≤ τ ^ (2 * εT) / (34 * 10 ^ 7)
  hFmass : (bR * (1 / 100 / ρ0) * τ) ^ εF ≤
    bR * (τ ^ εT / ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈εT⁻¹⌉₊ + 3) -
      384 * (2312 * τ ^ (-εT) / (1 / 100) ^ 2 * (bR * (1 / 100 / ρ0) * τ) ^ εF) *
        ((⌈εT⁻¹⌉₊ + 3 : ℕ) : ℝ))
  hFvol : bR ^ 3 * (1 / 100 / ρ0) ^ 2 * (3072 * ρc ^ 2 * τ ^ (-εT) * τ ^ (σ - ε1)) ≤
    ρc ^ tF * (bR * (1 / 100 / ρ0) * τ) ^ (σ - εF)
  hτ'h : bR * (1 / 100 / ρ0) * τ ≤ bR * ρ0
  hτ'max : bR * (1 / 100 / ρ0) * τ ≤ τ'max
  hN1 : 1 ≤ ⌊1 / (64 * τ ^ (-ε1) * ρ0)⌋₊
  hNh : (⌊1 / (64 * τ ^ (-ε1) * ρ0)⌋₊ : ℝ) * (bR * ρ0) ≤ 1
  hNL : 8 * τ ^ (-ε1) * (2 * (ρ0 * (⌊1 / (64 * τ ^ (-ε1) * ρ0)⌋₊ + 2)) + 6 * τ) ≤ 1 / 2
  hmassN : (bR * (1 / 100 / ρ0) * τ) ^ η2 ≤
    (⌊1 / (64 * τ ^ (-ε1) * ρ0)⌋₊ : ℝ) * (bR * ρ0) / 7 *
      ((bR * (1 / 100 / ρ0) * τ) ^ εF * (bR * (1 / 100 / ρ0) * τ) ^ εF / 11648)
  hfin : ∀ δf : ℝ, (bR * (1 / 100 / ρ0) * τ) ^ c ≤ δf →
    δf ≤ (bR * (1 / 100 / ρ0) * τ) ^ (c - ε2) →
    bR * ρ0 ≤ δf ^ (-(ε / 8)) * δf ∧ δf ≤ δf ^ (-(ε / 8)) * (bR * ρ0) ∧
    1280 * τ ^ (-ε1) ≤ δf ^ (-(ε / 8)) ∧
    20800 * (δf ^ (-(ε / 8))) ^ 3 * (4 ^ (1 - σ) * τ ^ (-ε1)) ≤ δf ^ (-ε) ∧ δf ≤ d0 ∧
    1280 * τ ^ (-ε1) ≤ δf ^ (-ε)

/-- Global grains from an extremal family with a Lipschitz plane map and local grains, given
its two-scale decomposition and the volume lower bound at the coarse scale. -/
theorem gg_from_tau {σ ε c ε2 η2 εF εT ε1 tF τ ρc d0 τ'max : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 ≤ ε) (hε2ε : ε2 ≤ ε)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 100) (hε1T : ε1 ≤ εT) (hεT : 0 < εT) (hεF : 0 < εF)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : Family ε1 τ n x v Y) (hS : Separated ε1 τ n x v)
    (hvol : volume (⋃ i, Y i) ≤ ENNReal.ofReal (τ ^ (σ - ε1)))
    {V : Space → Space} (hV1 : ∀ p, p ∈ (⋃ i, Y i) → ‖V p‖ = 1)
    (hVv : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ τ)
    (hVL : ∀ p q, p ∈ (⋃ i, Y i) → q ∈ (⋃ i, Y i) → dist (V p) (V q) ≤ τ ^ (-ε1) * dist p q)
    (hloc : ∀ ρ : ℝ, τ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
      Covering ρ (1 - σ) (τ ^ (-ε1))
        ((fun q : Space => inner ℝ (V p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))
    (hTS : TwoScaleAt σ εT τ ρc n x v Y)
    (hlow : ∀ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family εT ρc m x' v' Y' → Separated εT ρc m x' v' →
        ENNReal.ofReal (ρc ^ tF) < volume (⋃ q, Y' q))
    (hPGT : ∀ τ' : ℝ, 0 < τ' → τ' ≤ τ'max → τ' ≤ 1 / 100 → PGTAt σ c ε2 η2 τ')
    (hεFη2 : εF ≤ η2)
    (hnum : ∀ ρ0, ρc / 16 ≤ ρ0 → ρ0 ≤ ρc → τ ≤ ρ0 →
      GGNum σ ε c ε2 η2 εF εT ε1 tF τ ρc ρ0 d0 τ'max) :
    WeakGrainsAt σ ε d0 := by
  classical
  obtain ⟨Y', k, z, w, Yt, a, s, M, hY'Y, hY'm, hmass', hFamc, hSepc, -, hcover, -, hs, hYt,
    -, -, -, -, -, ⟨ρ0, k0, z0, w0, g, hτρ0, hρ0c, hρ0c', hg, -, hw0, -, huniq0, -, -, hfrost0,
      hdil0, hY'0⟩, -, -, -, ⟨θ, hθ, hP3⟩⟩ := hTS
  obtain ⟨hρc, hloc1, hloc2, hsmall, hC2a, hC2b, hFmass, hFvol, hτ'h, hτ'max, hN1, hNh, hNL,
    hmassN, hfin⟩ := hnum ρ0 hρ0c hρ0c' hτρ0
  obtain ⟨hn, hv, hball, hhalf, hYm, hYT, -⟩ := id hF
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le hτ hτρ0
  have hρ0100 : ρ0 ≤ 1 / 100 := hρ0c'.trans (hρc.trans (by norm_num))
  -- the lower bound at the coarse scale for the coarse family
  have hlowc : ENNReal.ofReal (ρc ^ tF) < volume (⋃ j, Yt j) := hlow k z w Yt hFamc hSepc
  -- one rescaled fibre
  set tsel : ℝ := 2312 * τ ^ (-εT) / (1 / 100) ^ 2 * (bR * (1 / 100 / ρ0) * τ) ^ εF with htsel
  have htselpos : 0 < tsel := by rw [htsel]; have := bR_pos; positivity
  have hC2c : 2312 * τ ^ (-εT) / (1 / 100) ^ 2 / tsel ≤ (bR * (1 / 100 / ρ0) * τ) ^ (-εF) := by
    have hb := bR_pos
    rw [htsel, Real.rpow_neg (by positivity : (0 : ℝ) ≤ bR * (1 / 100 / ρ0) * τ)]
    apply le_of_eq
    have h1 : 0 < τ ^ (-εT) := by positivity
    have h2 : 0 < (bR * (1 / 100 / ρ0) * τ) ^ εF := by positivity
    field_simp
  obtain ⟨j0, m, ι, hι, hιfib, hιgeo, hFamF, hSepF, hvolF⟩ :=
    fibre_extremal_core (σ := σ) (ε := εT) (η := ε1) (t := tF) (ε' := εF) (b := bR) hτ hτ1 hε1T hεT
      hF hS hvol hY'Y hY'm hmass' hFamc hcover hs hYt hθ hP3 hτρ0 hρ0c' hg hw0 huniq0 hfrost0
      hdil0 hY'0 hlowc hρc rfl hsmall hC2a hC2b hC2c htselpos hFmass hFvol
  -- the global grains from the rescaled fibre
  have hτ'0 : 0 < bR * (1 / 100 / ρ0) * τ := by have := bR_pos; positivity
  have hτ'1 : bR * (1 / 100 / ρ0) * τ ≤ 1 := hsmall.trans (by norm_num)
  set E : Set Space := ⋃ i, Y i with hE
  have hlocE : ∀ p ∈ E, Covering ((5 * ρ0) ^ 2) (1 - σ) (τ ^ (-ε1))
      ((fun q => ⟪V p, q⟫) '' (E ∩ ball p (5 * ρ0))) := by
    intro p hp
    have := hloc ((5 * ρ0) ^ 2) hloc1 hloc2 p hp
    rwa [Real.sqrt_sq (by positivity)] at this
  exact gg_after_fibre (εF := εF) (b := bR) (L := τ ^ (-ε1)) (C := τ ^ (-ε1)) hσ0.le hσ1 hε hε2ε
    hτ hτρ0 hρ0100 half_le_bR bR_le_one (by positivity) (by positivity) hτ'0 hτ'h hτ'1
    (fun p hp => hV1 p hp) (fun p hp q hq => hVL p q hp hq) hlocE (hw0 j0) hv ι
    (fun q => (hY'Y (ι q)).trans (subset_iUnion Y (ι q)))
    (fun q => (hY'Y (ι q)).trans (hYT (ι q))) hιfib
    (fun q p hp => hVv (ι q) p (hY'Y (ι q) hp)) hFamF hSepF hvolF
    (hPGT _ hτ'0 hτ'max (hsmall.trans (by norm_num))) hεFη2 hN1 hNh hNL hmassN hfin

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
