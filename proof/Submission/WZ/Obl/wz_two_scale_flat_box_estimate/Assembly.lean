-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.LocalPacket
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.GlobalSelection
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.CoarseBoxSlabs

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridKeys gridCell gridUnion gridUnion_measurable gridUnion_volume_ne_top gridCell_volume
    gridCell_volume_ne_top gridUnion_product)
open WangZahlLot.Obl.wz_flat_factored_improvement (BodySlabCount BodyConvexCount)

set_option maxHeartbeats 1600000 in
/-- Quantitative assembly with an explicit error budget. All losses are powers
of D; the final parameter choice makes them smaller than the requested error. -/
theorem two_scale_assembly {σ ω ε t Af Ac ηf ηc df dc δ s D ρ a b c : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hAf : 0 < Af) (hAc : 0 < Ac)
    (Hf : FineBoxBound σ ω t Af ηf df) (Hc : CoarseBoxBound σ ω t Ac ηc dc)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδdf : δ ≤ df) (hδdc : δ ≤ dc)
    (hDeq : D = δ ^ (-s)) (hD : 512 ≤ D)
    (hδρ : δ ≤ ρ) (hρa : ρ ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : 1 ≤ c) (hc8 : c ≤ 8) (haSmall : a ≤ 1 / 100)
    (K Kc : ℕ) (hK : 0 < K) (hreg : 224 * (K : ℝ) ≤ D)
    (hlog : (10 : ℝ) ^ (16 : ℕ) * (Kc + 1 : ℕ) ≤ D)
    (hbottom : (1 / 2 : ℝ) ^ Kc ≤ δ / 16)
    (hcut : 432 * (1 / D) ^ K * a * b ≤ (1 / D ^ (2 : ℕ)) * δ ^ 2 / 2)
    (hηf : δ ^ ηf ≤ 1 / D ^ (3 : ℕ)) (hηc : δ ^ ηc ≤ 1 / D ^ (19 : ℕ))
    (herror : δ ^ ε ≤ δ ^ (2 * t) / D ^ (45 : ℕ))
    {n N L : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (y w : Fin N → Space) (f : Fin n → Fin N)
    (z : Fin L → Space) (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L)
    (hA : Admissible δ s (δ ^ (-s)) (δ ^ (-s)) n x v Y)
    (hC : Cover δ s n x v Y .univ Y ρ N y w f)
    (hB : BoxCover δ s ρ a b c N L y w z e g)
    (hnmax : (n : ℝ) ≤ δ ^ (-100 : ℝ)) :
    ENNReal.ofReal (bound σ ω ε (Af * Ac) δ a b n) ≤ volume (⋃ i, Y i) := by
  classical
  obtain ⟨hn, hfine, hdist, hmass, hconv, hslab⟩ := hA
  obtain ⟨_, _, hw, hcontain, _, hbelow, hfbal, _, _⟩ := hC
  have hDpos : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδa : δ ≤ a := hδρ.trans hρa
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) (f ⟨0, hn⟩).isLt
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le _) (g (f ⟨0, hn⟩)).isLt
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hDensityPower : δ ^ s = 1 / D := by rw [hDeq, Real.rpow_neg hδ.le]; simp
  have hfbalD : ∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ D * Set.ncard {i | f i = k'} := by
    simpa only [← hDeq, Finset.mem_univ, true_and] using hfbal
  have hgbalD : ∀ k k', (Set.ncard {i | g i = k} : ℝ) ≤ D * Set.ncard {i | g i = k'} := by
    simpa only [← hDeq] using hB.2.1
  have hconvD : WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount δ D n x v := by
    simpa only [hDeq] using hconv
  have hslabD : SlabCount δ D n x v := by simpa only [hDeq] using hslab
  have hbelowD : BelowSlab δ ρ D n N x v .univ y w f := by simpa only [hDeq] using hbelow
  have hcontain' (i : Fin n) : Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i)) :=
    hcontain i (Finset.mem_univ _)
  have hfsurj := balanced_assignment_surjective hn f hfbalD
  have hgsurj := balanced_assignment_surjective hN g hgbalD
  have hparentsMeet := assigned_parents_meet_ball hδ x v y w f hfsurj
    (fun i => (hfine i).2.1) hcontain'
  obtain ⟨m, j, hm, hj, hret, hden⟩ := select_dense_fine_with_budget (D := D) hδ hδ1 (by linarith)
    hn x v Y (fun i => (hfine i).1) (fun i => (hfine i).2.2.2)
    (fun i => (hfine i).2.2.2.trans (hfine i).2.1) (by simpa only [hDensityPower] using hmass)
  obtain ⟨F, q, k, hF, hq, hk, hmin, hmax, hsize, hlocal, hparent, hbudget⟩ :=
    select_box_fibers (D := D) hn hN hL f g j hj (by linarith) hfbalD hgbalD hret
  have hFreal : (0 : ℝ) < F := by exact_mod_cast hF
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  let Fmax : ℝ := D * n / N
  have hFmax : 0 < Fmax := by dsimp [Fmax]; positivity
  let h : Fin m → Fin L := fun i => g (f (j i))
  let M := fun l : Fin q => fiberSize h (k l)
  let I := fun l : Fin q => j ∘ fiberIndex h (k l)
  let J := fun l : Fin q => fiberIndex g (k l)
  let fLocal := fun l : Fin q => fiberParent (f ∘ j) g (k l)
  have hIinj (l : Fin q) : Function.Injective (I l) := hj.comp (fiberIndex_injective h (k l))
  have hJinj (l : Fin q) : Function.Injective (J l) := fiberIndex_injective g (k l)
  have hIG (l : Fin q) (i : Fin (M l)) : f (I l i) = J l (fLocal l i) :=
    (fiberParent_spec (f ∘ j) g (k l) i).symm
  have hIbox (l : Fin q) (i : Fin (M l)) : g (f (I l i)) = k l := fiberIndex_spec h (k l) i
  have hJbox (l : Fin q) (p : Fin (fiberSize g (k l))) : g (J l p) = k l := fiberIndex_spec g (k l) p
  have hlocalM (l : Fin q) : (F : ℝ) ≤ D ^ (3 : ℕ) * M l := by
    simpa only [M, h, fiberSize_eq] using hlocal l
  have hM (l : Fin q) : 0 < M l := by
    have hh : (0 : ℝ) < M l := (mul_pos_iff_of_pos_left (pow_pos hDpos 3)).mp
      (hFreal.trans_le (hlocalM l))
    exact_mod_cast hh
  have hMmax (l : Fin q) : (M l : ℝ) ≤ δ ^ (-100 : ℝ) := by
    have hh : M l ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (I l) (hIinj l)
    exact (Nat.cast_le.mpr hh).trans hnmax
  have hlocalPackets (l : Fin q) : ∃ S : Finset (Fin 3 → ℤ), S ⊆ gridKeys a ∧
      gridUnion a S ⊆ Box (6 * a) (6 * b) (6 * c) (z (k l)) (e (k l)) ∧
      ENNReal.ofReal (a * b / D ^ (19 : ℕ)) ≤ volume (gridUnion a S) ∧
      ∀ u ∈ S, cellProfile σ ω t Af δ a b F D * a ^ 3 ≤
        volume.real ((⋃ i, Y (I l i)) ∩ gridCell a u) := by
    apply local_box_packet hσ hσhalf hAf Hf hδ hδdf hδa hρ hρa hab hbc hc hc8 haSmall
      (by linarith) hFreal hFmax K Kc hK hreg hlog hbottom hcut hηf
      (z (k l)) (e (k l)) (hM l) (x ∘ I l) (v ∘ I l) (Y ∘ I l)
      (y ∘ J l) (w ∘ J l) (fLocal l) (hMmax l)
      (fun i => (hfine (I l i)).1) (fun i => (hfine (I l i)).2.1)
      (fun i i' hii => hdist (I l i) (I l i') (fun he => hii (hIinj l he)))
      (fun i => (hfine (I l i)).2.2.1) (fun i => (hfine (I l i)).2.2.2)
      (fun i => hden (fiberIndex h (k l) i))
      (convexCount_subfamily x v hconvD (I l) (hIinj l)) (fun p => hw (J l p))
    · intro i
      simpa only [Function.comp_apply, ← hIG] using hcontain' (I l i)
    · intro p
      simpa only [Function.comp_apply, hJbox] using hB.1 (J l p)
    · exact fun p => hparentsMeet (J l p)
    · simpa only [← hDeq, J, Function.comp_apply] using
        box_fiber_raw_count hδ ha hb hcpos y w z e g hB (k l)
    · exact belowSlab_subfamily hρ hDpos.le x v y w f hbelowD hcontain' hparent
        (I l) (hIinj l) (J l) (fLocal l) (hIG l)
    · intro p
      have hh : Set.ncard {i | fLocal l i = p} ≤ Set.ncard {i | f (I l i) = J l p} := by
        apply Set.ncard_mono
        intro i hi
        change f (I l i) = J l p
        rw [hIG, hi]
      exact (Nat.cast_le.mpr hh).trans
        ((Nat.cast_le.mpr (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.count_subfamily
          (I l) (hIinj l) (fun i => f i = J l p))).trans (hparent (J l p)))
    · exact hlocalM l
    · simpa only [fiberSize_eq] using hbudget (k l)
  choose S hS hSP hSd hScell using hlocalPackets
  have hqmax : (q : ℝ) ≤ δ ^ (-100 : ℝ) := by
    have hqL : q ≤ L := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective k hk
    have hLN : L ≤ N := by simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective g hgsurj
    have hNn : N ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective f hfsurj
    exact (Nat.cast_le.mpr (hqL.trans (hLN.trans hNn))).trans hnmax
  have hboxesMeet (l : Fin q) : (Box a b c (z (k l)) (e (k l)) ∩ ball (0 : Space) 1).Nonempty := by
    obtain ⟨p, hp⟩ := hgsurj (k l)
    obtain ⟨u, hu, hub⟩ := hparentsMeet p
    exact ⟨u, by simpa only [hp] using hB.1 p hu, hub⟩
  have hboxconv : BodyConvexCount (fun l => Box a b c (z (k l)) (e (k l))) (a * b * c) D := by
    apply bodyConvexCount_subfamily (by positivity) (fun l => Box a b c (z l) (e l)) _ k hk
    simpa only [← hDeq, BodyConvexCount] using hB.2.2.2.1
  have hboxslab0 := coarse_box_slabs hDpos.le hFreal (by positivity : 0 ≤ D ^ (9 : ℕ))
    x v (fun l => coarseBox a b c (z (k l)) (e (k l))) (fun i l => g (f i) = k l)
    (fun i => (hfine i).2.1) hslabD (fun l => Nat.cast_le.mpr (hmin (k l)))
    (by
      intro i
      have hh : Set.ncard {l | g (f i) = k l} ≤ 1 := by
        apply Set.ncard_le_one_iff_subsingleton.mpr
        intro l hl l' hl'
        exact hk (hl.symm.trans hl')
      exact_mod_cast hh)
    (by nlinarith only [hsize])
    (by
      intro i l hil
      apply image_mono
      apply (hcontain' i).trans
      apply (hB.1 (f i)).trans
      rw [hil]
      exact box_subset_sixfold ha.le hb.le hcpos.le _ _)
  have hboxslab : BodySlabCount (fun l => coarseBox a b c (z (k l)) (e (k l))) (D ^ (11 : ℕ)) := by
    intro u t' r hu hr
    have hcoef : 512 * D ^ (9 : ℕ) * D ≤ D ^ (11 : ℕ) := by
      nlinarith only [mul_le_mul_of_nonneg_right hD (by positivity : 0 ≤ D ^ 10)]
    exact (hboxslab0 u t' r hu hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg q)) hr.le))
  have hcoarseDen (l : Fin q) : ENNReal.ofReal (δ ^ ηc * (a * b)) ≤ volume (gridUnion a (S l)) := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans (hSd l)
    have hh := mul_le_mul_of_nonneg_right hηc (mul_nonneg ha.le hb.le)
    convert hh using 1 <;> ring
  have hcoarse := Hc δ a b c D (D ^ (11 : ℕ)) hδ hδdc hδa hab hbc hc hc8 hD1 (one_le_pow₀ hD1)
    q (z ∘ k) (e ∘ k) (fun l => gridUnion a (S l)) hq hqmax hboxesMeet
    (fun l => gridUnion_measurable a (S l)) hSP hcoarseDen hboxconv hboxslab
  let θ := cellProfile σ ω t Af δ a b F D
  have hθ : 0 < θ := cellProfile_pos hAf hδ ha hb hFreal hDpos
  let Sall := Finset.univ.biUnion S
  have hUnion : gridUnion a Sall = ⋃ l, gridUnion a (S l) := by
    ext p
    simp only [gridUnion, Sall, mem_iUnion, Finset.mem_biUnion, Finset.mem_univ,
      true_and, exists_prop]
    constructor
    · rintro ⟨u, ⟨l, hu⟩, hp⟩
      exact ⟨l, u, hu, hp⟩
    · rintro ⟨l, u, hu, hp⟩
      exact ⟨u, ⟨l, hu⟩, hp⟩
  have hScellGlobal : ∀ u ∈ Sall, ENNReal.ofReal θ * volume (gridCell a u) ≤ volume ((⋃ i, Y i) ∩ gridCell a u) := by
    intro u hu
    obtain ⟨l, _, hul⟩ := Finset.mem_biUnion.mp hu
    rw [gridCell_volume ha.le, ← ENNReal.ofReal_mul hθ.le]
    apply (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top (gridCell_volume_ne_top ha u) (measure_mono inter_subset_right))).mpr
    exact (hScell l u hul).trans (ENNReal.toReal_mono
      (ne_top_of_le_ne_top (gridCell_volume_ne_top ha u) (measure_mono inter_subset_right))
      (measure_mono (inter_subset_inter_left _ (iUnion_subset fun i => subset_iUnion Y (I l i)))))
  have hproduct := gridUnion_product ha Sall (⋃ i, Y i)
    (MeasurableSet.iUnion fun i => (hfine i).2.2.1) (ENNReal.ofReal θ) hScellGlobal
  rw [hUnion] at hproduct
  have hcoarse' := (ENNReal.ofReal_le_ofReal (coarse_scalar_lower hσ hσhalf hAc hδ ha hb hc hD1 hqreal)).trans hcoarse
  have hfull := (mul_le_mul' (le_refl (ENNReal.ofReal θ)) hcoarse').trans hproduct
  rw [← ENNReal.ofReal_mul hθ.le] at hfull
  have hprofile := profile_product (σ := σ) (ω := ω) (ε := t) hAf hAc hδ ha hb hFreal hDpos hqreal
  change θ * _ = _ at hprofile
  rw [hprofile] at hfull
  exact (ENNReal.ofReal_le_ofReal (final_profile_lower hσ hσhalf (mul_pos hAf hAc) hδ hδ1
    ha hb hD1 hnreal hqreal hFreal hsize herror)).trans hfull

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
