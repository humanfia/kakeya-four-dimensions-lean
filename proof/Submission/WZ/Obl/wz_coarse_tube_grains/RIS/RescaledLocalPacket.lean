-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledLocalPacket.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledLocalPlanar
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.AnisotropicPlanarPacket
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.UniformPackingPieces
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PacketRescaledLocality
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PacketPower

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_extremal_lipschitz_grains wz_affine_robust_cluster_estimate
open scoped Classical

set_option maxHeartbeats 1400000 in
/-- Relative broadness and a thin ellipsoidal cell give actual physical
prism packets with arbitrary power losses and exact crossing geometry. -/
theorem rescaled_local_prism_packet {ζ β D : ℝ} (hζ : 0 < ζ) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ ζ / 3 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ r ρ c : ℝ, 0 < δ → ∀ hρ : 0 < ρ, ρ ≤ 1 / 256 →
      0 < c → c ≤ 1 / 256 → 512 * c ≤ r → r ≤ 1 → 16 * δ ≤ 128 * ρ * c →
      let ξ := δ / (100 * ρ)
      ξ ≤ 1 / 100 → ξ ≤ d → 2560 * c ≤ ξ ^ (η + ζ / 3) * r →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (p₀ y w : V)
        (E : V ≃ₗᵢ[ℝ] V), E w = axis →
      let F := rescaleMap E y w (by norm_num : (0 : ℝ) < 1 / 100) hρ
      0 < n → (n : ℝ) ≤ ξ ^ (-D) → ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) →
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ T δ (x i) (v i) ∩ F ⁻¹' ball (F p₀) (r / 100)) →
      (∀ i, T δ (x i) (v i) ⊆ T ρ y w) →
      o (ξ ^ η * n * δ ^ 2 * r) ≤ ∑ i, μ (Y i) →
      μ (⋃ i, Y i) ≤ o (ξ ^ (-η) * δ * ρ * r ^ 2) →
      (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        ({i | p ∈ Y i ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
          (ξ ^ (-η) * (s / ρ) ^ β) * incidence Y p) →
      Nonempty (LocalPrismPacket δ r ρ c ζ x v Y p₀ y w) := by
  let ε := ζ / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  have h3ε : 3 * ε = ζ := by dsimp [ε]; ring
  obtain ⟨η₀, hη₀, hη₀1, d₀, hd₀, hplanar⟩ := BrushPlanarity.rescaled_local_planar hε hβ hD
  obtain ⟨K, hK, hpacket⟩ := anisotropic_planar_packet_prisms
  obtain ⟨d₁, hd₁, huniform⟩ := packing_prism_uniform_refinement hD hε
  obtain ⟨d₂, hd₂, hconstant⟩ := fixed_constant_power_bound
    (C := 320256 * (K : ℝ)) (by positivity) hε
  let η := min η₀ ε
  have hη : 0 < η := lt_min hη₀ hε
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  refine ⟨η, hη, hηη₀.trans hη₀1, min_le_right _ _,
    min d₀ (min d₁ d₂), lt_min hd₀ (lt_min hd₁ hd₂), ?_⟩
  intro δ r ρ c hδ hρ hρ256 hc hc256 hcr hr1 hsize ξ hξ100 hξd hbudget
    n x v Y p₀ y w E hew F hn hnD hw hv hY hYT hcover hdense hvol hbroad
  have hr : 0 < r := by linarith
  have hρ1 : ρ ≤ 1 := by linarith
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξ1 : ξ ≤ 1 := by linarith
  have hδξ : δ ≤ ξ := by
    apply (le_div_iff₀ (by positivity : 0 < 100 * ρ)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hρ256 hδ.le]
  have hδρr : δ ≤ ρ * r := by
    have hh := mul_le_mul_of_nonneg_left hcr hρ.le
    nlinarith
  have hpospow : ξ ^ η₀ ≤ ξ ^ η := Real.rpow_le_rpow_of_exponent_ge hξ hξ1 hηη₀
  have hnegpow : ξ ^ (-η) ≤ ξ ^ (-η₀) :=
    Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (neg_le_neg hηη₀)
  have hdense₀ : o (ξ ^ η₀ * n * δ ^ 2 * r) ≤ ∑ i, μ (Y i) := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hdense
    gcongr
  have hvol₀ : μ (⋃ i, Y i) ≤ o (ξ ^ (-η₀) * δ * ρ * r ^ 2) := by
    apply hvol.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
  have hbroad₀ : ∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
      ({i | p ∈ Y i ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
        (ξ ^ (-η₀) * (s / ρ) ^ β) * incidence Y p := by
    intro p u s hu hs hsρ
    apply (hbroad p u s hu hs hsρ).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnegpow
      (Real.rpow_nonneg (div_nonneg (hδ.le.trans hs) hρ.le) _)) (incidence_nonneg Y p)
  obtain ⟨u, t, M, Y₁, hu, hM, hY₁, hslab, hnormal, hretain, hvol₁, hlevel⟩ :=
    hplanar δ ρ r hδ hρ hρ1 hδρr hr1 hξ100 (hξd.trans (min_le_left _ _))
      n x v Y y w p₀ E hew hn hnD hw hv hY hYT hcover hdense₀ hvol₀ hbroad₀
  change o (ξ ^ ε) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Y₁ i) at hretain
  change o (ξ ^ ε * δ * ρ * r ^ 2) ≤ μ (⋃ i, Y₁ i) at hvol₁
  have hY₁T (i : Fin n) : Y₁ i ⊆ T δ (x i) (v i) ∩ F ⁻¹' ball (F p₀) (r / 100) :=
    ((hY₁ i).2).trans (hYT i)
  have hY₁ball (i : Fin n) : Y₁ i ⊆ ball p₀ r := by
    intro p hp
    apply rescale_preimage_ball_subset_ball E y w (by norm_num : (0 : ℝ) < 1 / 100) hρ hρ1 p₀
    change p ∈ F ⁻¹' ball (F p₀) ((1 / 100 : ℝ) * r)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (hY₁T i hp).2
  have hQ : {i | (Y₁ i).Nonempty}.Nonempty := by
    by_contra hQ
    have hz (i : Fin n) : Y₁ i = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (fun hi => hQ ⟨i, hi⟩)
    have hpos : (0 : ENNReal) < o (ξ ^ ε * δ * ρ * r ^ 2) := by
      apply ENNReal.ofReal_pos.mpr
      positivity
    exact hpos.not_ge (by simpa only [μ, hz, iUnion_empty, measure_empty] using hvol₁)
  have hshape (i : Fin n) : Y₁ i ⊆ {p | ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ ≤ ρ * r ∧
      |inner ℝ w (p - p₀)| ≤ r ∧ |inner ℝ u p - t| ≤ 20 * δ} := by
    intro p hp
    have hball : ‖F p - F p₀‖ ≤ (1 / 100 : ℝ) * r := by
      have hh : ‖F p - F p₀‖ ≤ r / 100 := by
        exact (show ‖F p - F p₀‖ < r / 100 by
          simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using (hY₁T i hp).2).le
      simpa only [dist_eq_norm, div_eq_mul_inv, one_mul, mul_comm] using hh
    have hh := rescale_ball_axial_transverse E (y := y) hew (by norm_num : (0 : ℝ) < 1 / 100)
      hρ hρ1 hr.le p p₀ hball
    exact ⟨hh.2.2, hh.2.1, hslab i ⟨p, hp⟩ (hY₁T i hp)⟩
  have hdense₁ : o ((ξ ^ (η + ε) * r) * n * δ ^ 2) ≤ ∑ i, μ (Y₁ i) := by
    calc
      _ = o (ξ ^ ε) * o (ξ ^ η * n * δ ^ 2 * r) := by
        dsimp only [o]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hξ.le _), Real.rpow_add hξ]
        congr 1
        ring
      _ ≤ o (ξ ^ ε) * ∑ i, μ (Y i) := mul_le_mul_right hdense _
      _ ≤ _ := hretain
  have hvol₁' : o ((ξ ^ ε / 16) * ((16 * δ) * ρ * r ^ 2)) ≤ μ (⋃ i, Y₁ i) := by
    convert hvol₁ using 1
    congr 1
    ring
  have hmult (p : V) : multiplicity Y₁ p = o (incidence Y₁ p) := by
    rw [multiplicity_eq_ncard, incidence_eq_ncard]
    exact (ENNReal.ofReal_natCast _).symm
  have hlower : ∀ p ∈ ⋃ i, Y₁ i, o M ≤ multiplicity Y₁ p := by
    intro p hp
    rw [hmult]
    exact ENNReal.ofReal_le_ofReal (hlevel p hp).1
  have hupper : ∀ p, multiplicity Y₁ p ≤ 2 * o M := by
    intro p
    rw [hmult]
    have hpoint : incidence Y₁ p ≤ 2 * M := by
      by_cases hp : p ∈ ⋃ i, Y₁ i
      · exact (hlevel p hp).2
      · rw [incidence_eq_zero_of_notMem Y₁ hp]
        positivity
    calc
      _ ≤ o (2 * M) := ENNReal.ofReal_le_ofReal hpoint
      _ = _ := by simp [o, ENNReal.ofReal_mul]
  obtain ⟨e, F₀, Y₂, H₀, he0, hew', hY₂, hdisj₀, hH₀, hunion₀, hmass₀, _, hcross₀⟩ :=
    hpacket δ ρ c (ξ ^ (η + ε) * r) (ξ ^ ε / 16) t r hδ hρ hr hρ256 hc hc256 hcr
      hsize hbudget (by positivity) n x v Y₁ y w u p₀ hw hu hQ
      (fun i => ⟨hv i, (hY₁ i).1, (hY₁T i).trans inter_subset_left⟩)
      (fun i _ => hcover i) hshape hnormal hdense₁ hvol₁'
      (o M) (ENNReal.ofReal_pos.mpr hM).ne' ENNReal.ofReal_ne_top hlower hupper
  have hframe : |e w 1| ≤ 10 * ρ := by
    nlinarith [sq_nonneg (e w 0), sq_abs (e w 1), abs_nonneg (e w 1)]
  have hslab₂ : (⋃ i, Y₁ i) ⊆ {p | ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ ≤ ρ * r ∧
      |inner ℝ w (p - p₀)| ≤ r ∧ |e (p - p₀) 0 - (t - inner ℝ u p₀)| ≤ 20 * δ} := by
    intro p hp
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    have hh := hshape i hpi
    refine ⟨hh.1, hh.2.1, ?_⟩
    have he : e (p - p₀) 0 - (t - inner ℝ u p₀) = inner ℝ u p - t := by
      rw [he0, inner_sub_right]
      ring
    rw [he]
    exact hh.2.2
  have hmeet (z : V) (hz : z ∈ F₀) : (P (16 * δ) (128 * ρ * c) c z e ∩
      {p | ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ ≤ ρ * r ∧
        |inner ℝ w (p - p₀)| ≤ r ∧ |e (p - p₀) 0 - (t - inner ℝ u p₀)| ≤ 20 * δ}).Nonempty := by
    obtain ⟨p, hp⟩ := (hH₀ z hz).2.2.1
    have hpY : p ∈ ⋃ i, Y₂ i := hunion₀ ▸ mem_iUnion₂.mpr ⟨z, hz, hp⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpY
    exact ⟨p, (hH₀ z hz).2.1 hp, hslab₂ (mem_iUnion.mpr ⟨i, (hY₂ i).2 hi⟩)⟩
  have hpacking : o ((F₀.card : ℝ) * ((16 * δ) * (128 * ρ * c) * c)) ≤
      o (10008 * ((16 * δ) * ρ * r ^ 2)) := by
    have hh := prism_packing_in_anisotropic_slab hρ.le hρ1 hr.le (by positivity)
      (by positivity) hc.le (by positivity : 0 ≤ 20 * δ) (by linarith)
      (by gcongr; linarith) (by linarith) hw e hframe F₀ hdisj₀ hmeet
    convert hh using 1 <;> ring
  obtain ⟨k, F₁, Z, H, hFF, hHH, hZ, hdisj, hH, hunion, hmass, hden, hcross, huniformZ⟩ :=
    huniform ξ hξ ((hξd.trans (min_le_right _ _)).trans (min_le_left _ _)) n hnD
      (16 * δ) (128 * ρ * c) c 10008 ((16 * δ) * ρ * r ^ 2) (ξ ^ ε / 16)
      (by positivity) (by positivity) hc.le (by norm_num) (by positivity) e F₀ Y₁ Y₂ H₀
      (fun i z =>
        (∀ p ∈ T δ (x i) (v i) ∩ frontier (P (16 * δ) (128 * ρ * c) c z e),
          |e (p - z) 2| = c / 2) ∧
        (∀ s ∈ ({-c / 2, c / 2} : Set ℝ),
          ∃ p ∈ T δ (x i) (v i) ∩ P (16 * δ) (128 * ρ * c) c z e, e (p - z) 2 = s))
      (fun i => (hY₁ i).1) hY₂ hdisj₀ (fun z hz => ⟨(hH₀ z hz).1, (hH₀ z hz).2.1⟩)
      hpacking hunion₀ hcross₀ (o M) (K : ENNReal)
      (ENNReal.ofReal_pos.mpr hM).ne' ENNReal.ofReal_ne_top hlower hupper hmass₀ hvol₁'
  have hKbound : (320256 : ENNReal) * (K : ENNReal) ≤ o (ξ ^ (-ε)) := by
    have hh := ENNReal.ofReal_le_ofReal
      (hconstant ξ hξ ((hξd.trans (min_le_right _ _)).trans (min_le_right _ _)))
    simpa only [o, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 320256),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat] using hh
  have hinv : o (ξ ^ (-ε)) * o (ξ ^ ε) = 1 := by
    dsimp only [o]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hξ.le _), ← Real.rpow_add hξ]
    simp
  have hKbig : ((320256 : ENNReal) * K) * o (ξ ^ ε) ≤ 1 := by
    calc
      _ ≤ o (ξ ^ (-ε)) * o (ξ ^ ε) := mul_le_mul_left hKbound _
      _ = _ := hinv
  have hKsmall : (K : ENNReal) * o (ξ ^ ε) ≤ 1 := by
    refine le_trans ?_ hKbig
    exact mul_le_mul_left
      (show (K : ENNReal) ≤ 320256 * K by
        simpa only [one_mul] using mul_le_mul_left (by norm_num : (1 : ENNReal) ≤ 320256) (K : ENNReal)) _
  have hmass' : o (ξ ^ ζ) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Z i) := by
    have hh := triple_loss_absorption hξ hKsmall (hretain.trans hmass)
    simpa only [h3ε] using hh
  have hden' : o (ξ ^ ε) * o ((F₁.card : ℝ) * ((16 * δ) * (128 * ρ * c) * c)) ≤
      ((320256 : ENNReal) * K * o (ξ ^ (-ε))) * ∑ z ∈ F₁, μ (H z) := by
    calc
      _ = 16 * o ((ξ ^ ε / 16) * F₁.card * ((16 * δ) * (128 * ρ * c) * c)) := by
        dsimp only [o]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hξ.le _),
          ← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
        congr 1
        ring
      _ ≤ 16 * ((o (2 * 10008) * (K : ENNReal) * o (ξ ^ (-ε))) * ∑ z ∈ F₁, μ (H z)) :=
        mul_le_mul_right hden _
      _ = _ := by norm_num [o]; ring
  have hdensity' : o (ξ ^ ζ * F₁.card * ((16 * δ) * (128 * ρ * c) * c)) ≤
      ∑ z ∈ F₁, μ (H z) := by
    calc
      _ = o (ξ ^ (3 * ε)) * o ((F₁.card : ℝ) * ((16 * δ) * (128 * ρ * c) * c)) := by
        rw [h3ε]
        dsimp only [o]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hξ.le _)]
        congr 1
        ring
      _ ≤ _ := triple_loss_absorption hξ hKbig hden'
  have hbc : 128 * ρ * c ≤ c := by
    have hh := mul_le_mul_of_nonneg_right hρ256 hc.le
    nlinarith
  have hlocal (z : V) (hz : z ∈ F₁) : P (16 * δ) (128 * ρ * c) c z e ⊆ ball p₀ (3 * r) := by
    obtain ⟨p, hp⟩ := (hH z hz).2.2
    have hpZ : p ∈ ⋃ i, Z i := hunion ▸ mem_iUnion₂.mpr ⟨z, hz, hp⟩
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hpZ
    have hpball := hY₁ball i ((hY₂ i).2 ((hZ i).2 hpi))
    exact prism_subset_triple_ball (hsize.trans hbc) hbc hc.le (by linarith) e
      ⟨p, (hH z hz).2.1 hp, hpball⟩
  have hpow : δ ^ ζ ≤ ξ ^ ζ := Real.rpow_le_rpow hδ.le hδξ hζ.le
  refine ⟨{
    level := k
    frame := e
    centers := F₁
    shading := Z
    pieces := H
    aligned := hew'
    refines := fun i => ⟨(hZ i).1, ((hZ i).2).trans (((hY₂ i).2).trans (hY₁ i).2)⟩
    disjoint := hdisj
    piece_data := fun z hz => ⟨(hH z hz).1, (hH z hz).2.1, (hH z hz).2.2,
      (hH₀ z (hFF hz)).2.2.2, hlocal z hz⟩
    union_eq := hunion
    retains := (mul_le_mul_left (ENNReal.ofReal_le_ofReal hpow) _).trans hmass'
    density := (ENNReal.ofReal_le_ofReal (by gcongr)).trans hdensity'
    crossing := hcross
    uniform := huniformZ
  }⟩

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
