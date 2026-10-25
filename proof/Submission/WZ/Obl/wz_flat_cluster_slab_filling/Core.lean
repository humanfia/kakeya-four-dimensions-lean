-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.Core.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.PerTube
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Survival
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Numerics
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.CoreSteps
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Params

/-!
The proof of WZ Lemma 7.14, Steps 2-3, with the abbreviations of the frozen statement
unfolded (only the hypotheses that are used are kept).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

theorem core {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {e : ℝ} (he : 0 < e) :
    ∃ h : ℝ, 0 < h ∧ ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
      ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤ ∑ i, volume (Y i) →
    ∀ (ρ : ℝ) (S : Finset (Fin n)) (Z : Fin n → Set Space) (N : ℕ) (y w : Fin N → Space)
      (f : Fin n → Fin N),
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) →
      (∀ k, ‖w k‖ = 1) →
      (∀ i ∈ S, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i))) →
      δ ≤ ρ → ρ ≤ 1 →
      (∀ (k : Fin N) (p u : Space) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
        (({i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin n)).ncard
          : ℝ) ≤ δ ^ (-η) * (r / ρ) ^ β *
            (({i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : Set (Fin n)).ncard : ℝ)) →
      (∃ (G : Finset (Fin n)) (Z₁ : Fin n → Set Space) (u : Fin n → Space) (t r : Fin n → ℝ),
        G ⊆ S ∧ (∀ i, MeasurableSet (Z₁ i) ∧ Z₁ i ⊆ Z i ∧ (i ∉ G → Z₁ i = ∅)) ∧
        ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i ∈ G, volume (Z₁ i) ∧
        (∀ i ∈ G, ‖u i‖ = 1 ∧ Tube δ (x i) (v i) ⊆ Slab (u i) (t i) (r i) ∧
          r i ≤ δ ^ c * ρ) ∧
        ∀ i ∈ G, ∀ j ∈ G, f i = f j → (Z₁ i ∩ Z₁ j).Nonempty →
          Tube δ (x j) (v j) ⊆ Slab (u i) (t i) (r i)) →
      ∃ G' : Finset (Fin n), δ ^ e * n ≤ (G'.card : ℝ) ∧
        ∀ i ∈ G', ∃ (z : Space) (g : Space ≃ₗᵢ[ℝ] Space),
          Tube δ (x i) (v i) ⊆ Box (10 * δ) (δ ^ (1 - min c 1 / 2)) 2 z g ∧
          ENNReal.ofReal (δ ^ e) * volume (Box (10 * δ) (δ ^ (1 - min c 1 / 2)) 2 z g) ≤
            volume (Box (10 * δ) (δ ^ (1 - min c 1 / 2)) 2 z g ∩ ⋃ j, Y j) := by
  obtain ⟨d₀, hd₀, hd₀1, hnum⟩ := numerics hβ hc he
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min e c * min β 1 / 20 := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    have h1 : 0 < min e c := lt_min he hc
    have h2 : 0 < min β 1 := lt_min hβ one_pos
    rw [hε]; positivity
  refine ⟨ε, hεpos, ε, hεpos, d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd η hη hηε n x v Y hn hv hYm hYT hmass ρ S Z N y w f hZ hw hcoarse hδρ hρ1
    hbroad hFl
  obtain ⟨G, Z₁, u, t, r, hGS, hZ₁, hFlmass, hGslab, hnonint⟩ := hFl
  have hδ1 : δ ≤ 1 / 100 := hδd.trans hd₀1
  have hδ1' : δ ≤ 1 := by linarith
  have hρpos : 0 < ρ := lt_of_lt_of_le hδ hδρ
  -- the exponents
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ε + η := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = ε + 2 * η := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; linarith
  have hale : a ≤ 2 * (min e c * min β 1 / 20) := by rw [ha, ← hε]; linarith
  have ha'pos : 0 < a' := by rw [ha']; linarith
  have ha'le : a' ≤ 3 * (min e c * min β 1 / 20) := by rw [ha', ← hε]; linarith
  obtain ⟨N1, N2, N3, N4, N5, N6⟩ := hnum δ hδ hδd a a' hapos hale ha'pos ha'le
  have ha₀ : a = min e c * min β 1 / 20 + η := by rw [ha, hε]
  have ha'₀ : a' = min e c * min β 1 / 20 + 2 * η := by rw [ha', hε]
  -- the parameters
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = δ ^ a / 768 := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (δ ^ a' / 6144) ^ (1 / β) := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = ρ * τ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = δ ^ (1 - min c 1 / 2) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = b / (32 * ρ) := ⟨_, rfl⟩
  have hlampos : 0 < lam := by
    have := Real.rpow_pos_of_pos hδ a
    rw [hlam]; positivity
  have hbpos : 0 < b := by rw [hb]; exact Real.rpow_pos_of_pos hδ _
  have hLpos : 0 < L := by rw [hL]; positivity
  -- the inclusions
  have hZY : ∀ j, Z j ⊆ Y j := fun j => (hZ j).2.1
  have hZ₁Z : ∀ j, Z₁ j ⊆ Z j := fun j => (hZ₁ j).2.1
  have hZ₁T : ∀ j, Z₁ j ⊆ Tube δ (x j) (v j) := fun j => ((hZ₁Z j).trans (hZY j)).trans (hYT j)
  -- Step (i): regularization
  have hmass' : ENNReal.ofReal (384 * lam * n * δ ^ 2 + 384 * lam * δ ^ 2 * n) ≤
      ∑ i ∈ G, volume (Z₁ i) := by
    have hreal : 384 * lam * n * δ ^ 2 + 384 * lam * δ ^ 2 * n =
        δ ^ ε * (δ ^ η * n * δ ^ 2) := by
      rw [hlam, ha, Real.rpow_add hδ]; ring
    rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    calc ENNReal.ofReal (δ ^ ε) * ENNReal.ofReal (δ ^ η * n * δ ^ 2)
        ≤ ENNReal.ofReal (δ ^ ε) * ∑ i, volume (Y i) := by gcongr
      _ ≤ ∑ i ∈ G, volume (Z₁ i) := hFlmass
  obtain ⟨G2, Z2, hG2G, hZ2m, hZ2Z₁, hZ2mass, hZ2reg⟩ :=
    regularize (A := 384 * lam * n * δ ^ 2) hδ hδ1' hlampos.le hLpos (by positivity) x v hv G Z₁
      (fun j => (hZ₁ j).1) hZ₁T hmass'
  have hZ2Z : ∀ j, Z2 j ⊆ Z j := fun j => (hZ2Z₁ j).trans (hZ₁Z j)
  have hZ2Y : ∀ j, Z2 j ⊆ Y j := fun j => (hZ2Z j).trans (hZY j)
  -- Steps (ii)-(iii): survival
  have hTvol : ∀ j, volume (Tube δ (x j) (v j)) ≤ ENNReal.ofReal (384 * δ ^ 2) :=
    fun j => tube_volume_le hδ hδ1' (x j) (v j) (hv j)
  have hsh := survive_heavy (s := lam / 4) (B := 384 * δ ^ 2)
    (A := 384 * lam * n * δ ^ 2 / 2) (t := 48 * lam * δ ^ 2) (by positivity) (by positivity)
    (by positivity) S G2 f Z Z2 (fun j => (hZ j).1) hZ2m
    (fun j _ => (measure_mono ((hZY j).trans (hYT j))).trans (hTvol j))
    (fun j _ => (measure_mono ((hZ2Y j).trans (hYT j))).trans (hTvol j)) hZ2mass
  obtain ⟨G3, hG3⟩ : ∃ G3 : Finset (Fin n), G3 = G2.filter fun i =>
      ENNReal.ofReal (48 * lam * δ ^ 2) ≤ volume (Z2 i ∩ survivors S G2 f Z Z2 (lam / 4) i) :=
    ⟨_, rfl⟩
  rw [← hG3] at hsh
  have hcard : δ ^ e * n ≤ (G3.card : ℝ) := by
    have hδ2 : 0 < δ ^ 2 := by positivity
    have h1 : lam * n ≤ 8 * G3.card := by nlinarith
    have h2 : δ ^ e ≤ lam / 8 := by rw [hlam]; linarith [N1]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc δ ^ e * n ≤ lam / 8 * n := mul_le_mul_of_nonneg_right h2 hn0
      _ ≤ G3.card := by linarith
  refine ⟨G3, hcard, ?_⟩
  -- Step 3: the box of each heavy tube is filled
  intro i hi
  rw [hG3, Finset.mem_filter] at hi
  obtain ⟨hiG2, hiheavy⟩ := hi
  have hiG : i ∈ G := hG2G hiG2
  have hiS : i ∈ S := hGS hiG
  obtain ⟨hu, hslab, hrρ⟩ := hGslab i hiG
  have hδr : δ ≤ r i := slab_width_ge hδ hu hslab
  obtain ⟨-, hθpos, hθ1, hδθ, hθρ, -, hL3, hLle, hbδ, -, hb32, hr32, hr, hρL, hsmall, hnum'⟩ :=
    params hβ hc he hδ hδ1 hη hδr hrρ hρ1 ha₀ ha'₀ hlam hτ hθ hb hL N2 N3 N4 N5 N6
  have hZ3m : MeasurableSet (Z2 i ∩ survivors S G2 f Z Z2 (lam / 4) i) :=
    (hZ2m i).inter (survivors_measurable S G2 f Z Z2 (fun j => (hZ j).1) hZ2m _ i)
  have hZ3T : Z2 i ∩ survivors S G2 f Z Z2 (lam / 4) i ⊆ Tube δ (x i) (v i) :=
    Set.inter_subset_left.trans ((hZ2Y i).trans (hYT i))
  have hcross : ∀ p ∈ Z2 i ∩ survivors S G2 f Z Z2 (lam / 4) i, ∃ j, p ∈ Z2 j ∧
      Tube δ (x j) (v j) ⊆ Slab (u i) (t i) (r i) ∧
      θ < angle (v j) (v i) ∧ angle (v j) (v i) ≤ 8 * ρ ∧
      ENNReal.ofReal (lam / 16000) * volume (Tube δ (x j) (v j) ∩ ball p L) ≤
        volume (Z2 j ∩ ball p L) := by
    intro p hp
    obtain ⟨hp2, hpsurv⟩ := hp
    obtain ⟨j, hjG2, hfj, hpj, hang⟩ := crossing_exists S G2 f v Z Z2 (hG2G.trans hGS) hZ2Z
      hbroad hδθ hθρ (by positivity) hsmall i hiS (hv i) p (hZ2Z i hp2) hpsurv
    have hjG : j ∈ G := hG2G hjG2
    have hjS : j ∈ S := hGS hjG
    refine ⟨j, hpj, hnonint i hiG j hjG hfj.symm ⟨p, hZ2Z₁ i hp2, hZ2Z₁ j hpj⟩, hang, ?_,
      hZ2reg j p hpj⟩
    have h1 := coarse_angle hδ hρpos.le (hv j) (hw (f j)) (hcoarse j hjS)
    have h2 := coarse_angle hδ hρpos.le (hv i) (hw (f i)) (hcoarse i hiS)
    rw [hfj] at h1
    have h3 := angle_triangle (v j) (w (f i)) (v i)
    rw [angle_comm (w (f i)) (v i)] at h3
    linarith
  obtain ⟨z, g, hTbox, hfill⟩ := per_tube hδ hδ1 hρpos hθpos hθ1
    (by positivity : (0 : ℝ) ≤ lam / 16000) (by positivity : (0 : ℝ) ≤ 48 * lam) hb32 hL3 hLle
    hbδ x v Y hv hYm hYT i (u i) (t i) (r i) hu hslab hr32 hr hρL _ hZ3m hZ3T hiheavy Z2 hZ2m
    hZ2Y hcross hnum'
  rw [hb] at hTbox hfill
  exact ⟨z, g, hTbox, hfill⟩

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
