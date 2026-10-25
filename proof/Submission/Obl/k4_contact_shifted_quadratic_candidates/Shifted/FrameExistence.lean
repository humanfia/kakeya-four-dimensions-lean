import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.FinitePackets
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.FrameSource
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ContactRows
import Submission.Obl.k4_contact_shifted_quadratic_candidates.PaletteData
import Submission.Obl.k4_contact_shifted_quadratic_candidates.GridDepth

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open Set MeasureTheory Filter MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- Original simultaneous palettes provide the finite frame packets. Their
original assignment references are retained throughout history preparation. -/
theorem contact_frame_existence {α : Type} [MeasurableSpace α] {D : Data α}
    (h : ContactProblem D) : FrameExistence D := by
  classical
  let p := h.parameters
  have hN1 (k : ℕ) : 1 ≤ D.N k := by linarith [p.scale k]
  obtain ⟨U₁, hU₁, hU₁U, hpals⟩ := h.palettes
  refine ⟨U₁, hU₁, ?_⟩
  intro s₀ U' hs₀ hU' hsum hmargin
  let e' : ℝ := (D.e₀ - D.κ * s₀) / 2
  have he' : 0 < e' := by
    have hκ := p.rate_pos
    have he₀ := p.defect_pos
    dsimp only [e']
    nlinarith
  apply goodFrames_of_finite_packets D s₀ U' e' hN1 hU'
  intro m hm ε hε
  let σ : Fin (m + 1) → ℝ := fun r => s₀ + (r : ℝ) * (U' / m)
  let cap : ℕ → Fin (m + 1) := fun r => ⟨min r m, by omega⟩
  let depth : ℕ → ℝ := finiteGridDepth s₀ U' m
  have hdepth (r : ℕ) : s₀ ≤ depth r ∧ depth r ≤ s₀ + U' :=
    finiteGridDepth_bounds hU'.le hm r
  have hσ (r : Fin (m + 1)) : s₀ ≤ σ r ∧ σ r ≤ s₀ + U' := by
    simpa only [depth, finiteGridDepth_of_le s₀ U' (by omega : r.val ≤ m), σ] using hdepth r
  have hσgood (r : Fin (m + 1)) : 0 < σ r ∧ σ r ≤ U₁ :=
    ⟨hs₀.trans_le (hσ r).1, (hσ r).2.trans hsum⟩
  obtain ⟨H, hH1, hHsub, hpal⟩ := hpals (m + 1) σ hσgood
  let R : ℝ := 2 + (m : ℝ) + s₀⁻¹ + D.U
  have hR : 1 < R := by
    dsimp only [R]
    have := p.depth_pos
    have := inv_pos.mpr hs₀
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hR₀ : 0 < R := by linarith
  have hRinv : R⁻¹ ≤ s₀ := by
    have hh : s₀⁻¹ ≤ R := by dsimp only [R]; linarith [p.depth_pos, Nat.cast_nonneg (α := ℝ) m]
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hs₀) hh
  have hRk : (m : ℝ) + 2 ≤ R := by dsimp only [R]; linarith [p.depth_pos, inv_pos.mpr hs₀]
  have hRkinv : R⁻¹ ≤ ((m : ℝ) + 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (show 0 < (m : ℝ) + 2 by positivity) hRk
  have hdepthU (r : ℕ) : depth r ≤ D.U := (hdepth r).2.trans (hsum.trans hU₁U)
  have hcost := eventually_history_packet_cost D.N D.K H hN1 p.scale_limit
    p.subpower.1 hH1 p.subpower.2 hHsub m hε
  filter_upwards [hpal, h.atlas R hR, h.nested R hR,
    h.eventually_centered_rows (ε := ε / 2) (R := R) (by positivity) hR,
    hcost, p.subpower.2 e' he'] with k hkpal hkatlas hknest hkcenter hkcost hkcontact
  have hN : 0 < D.N k := by linarith [p.scale k]
  have hK1 : 1 ≤ D.K k := p.subpower.1 k
  have hK : 0 < D.K k := by linarith
  obtain ⟨hb, hν, hπ, hdom, hρ, hsupport, hrhomass, hP, hbnd, hPfit⟩ := h.basic k
  letI : IsProbabilityMeasure (D.ν k) := hν
  obtain ⟨M₀, L₀, hM₀, hmass₀⟩ := hkpal
  obtain ⟨M, L, hM1, hMbound, hentries⟩ := exists_uniform_palette_count
    (fun r => D.n k (σ r)) M₀ L₀ (hH1 k) hM₀
  let S : Set (α × ℝ) := dataPaletteSource D k σ (fun _ => M) L (H k)
  rw [← dataPaletteSource_eq_raw D k σ M₀ L₀ (H k)] at hmass₀
  have hsourceSub : dataPaletteSource D k σ M₀ L₀ (H k) ⊆ S :=
    finitePaletteSource_mono_entries (D.b k) (fun r => D.n k (σ r)) M₀ (fun _ => M)
      (fun r => D.B k (σ r)) L₀ L _ _ _ hentries
  have hmassS : ENNReal.ofReal ((D.K k)⁻¹ / 2) ≤ D.ρ k S :=
    hmass₀.trans (measure_mono hsourceSub)
  have grid (r : ℕ) := hkatlas (depth r) (hRinv.trans (hdepth r).1) (hdepthU r)
  have hSM : MeasurableSet S := by
    apply measurableSet_dataPaletteSource D k hb σ (fun _ => M) _ L (H k)
    intro r i
    exact ((hkatlas (σ r) (hRinv.trans (hσ r).1) ((hσ r).2.trans (hsum.trans hU₁U))).2.2.1 i).2.1
  have hSpoint (x : α × ℝ) (hx : x ∈ S) (r : Fin (m + 1)) :
      ∃ (i : Fin (D.n k (σ r))) (u : Fin M), x.1 ∈ D.B k (σ r) i ∧
        x.1 ∈ affineBlockFit (D.b k) (L r i u)
          (((D.j k (σ r) i : ℕ) : ℝ) / (2 : ℝ) ^ D.T k (σ r))
          ((((D.j k (σ r) i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T k (σ r))
          (H k * D.N k ^ (-σ r)) ∧
        x.2 ∈ Data.I (D.T k (σ r)) (D.j k (σ r) i) := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (mem_iInter.mp hx r)
    obtain ⟨u, hu⟩ := mem_iUnion.mp hi
    exact ⟨i, u, hu.1.1, hu.1.2, hu.2⟩
  have hSpos : 0 < D.ρ k S := (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hmassS
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hSpos.ne'
  obtain ⟨iD, uD, _⟩ := hSpoint x₀ hx₀ (cap 0)
  obtain ⟨anc, hanc⟩ := exists_finiteGrid_ancestors (D.n k) (D.A k)
    (fun s i => Data.I (D.T k s) (D.j k s i)) hU' hm
    (fun s t hss hst htu => hknest s t (hRinv.trans hss) hst (htu.trans (hsum.trans hU₁U)))
  let f₀ : Frame D k s₀ U' := {
    m := m
    M := M
    H := H k
    anc := anc
    pal := fun r i u => L (cap r) i u
    i₀ := iD
    u₀ := uD
    core := S }
  have hfirst : ∀ x ∈ S, ∀ r ≤ f₀.m, ∃ i u,
      x ∈ (D.A k (f₀.depth r) i ∩ f₀.entry r i u) ×ˢ f₀.block r i := by
    intro x hx r _
    obtain ⟨i, u, hxB, hxfit, hxt⟩ := hSpoint x hx (cap r)
    have hfit : x.1 ∈ affineFitSet (D.b k) (f₀.pal r i u)
        (f₀.left r i) (f₀.right r i) (f₀.H * D.N k ^ (-f₀.depth r)) := hxfit
    have hentry : x.1 ∈ ⋃ v, f₀.entry r i v := by
      change x.1 ∈ ⋃ v, assignedAffineEntry (D.b k) (D.B k (f₀.depth r) i)
        (f₀.pal r i) (f₀.left r i) (f₀.right r i) (f₀.H * D.N k ^ (-f₀.depth r)) v
      rw [iUnion_assignedAffineEntry]
      exact ⟨hxB, mem_iUnion.mpr ⟨u, hfit⟩⟩
    obtain ⟨v, hv⟩ := mem_iUnion.mp hentry
    exact ⟨i, v, ⟨((grid r).2.2.1 i).2.2 hxB, hv⟩, hxt⟩
  obtain ⟨i₀, u₀, C, hCm, hCne, hCS, hCparent, hCmass, hCcontact, hCcover, hCfloor⟩ :=
    frame_source_has_parent_core f₀ hK hM1 hν hb hdom hρ (h.contact k)
      (fun r i => ⟨((grid r).2.2.1 i).1, ((grid r).2.2.1 i).2.1⟩)
      (fun r => (grid r).2.2.2.1) hanc S hSM hfirst hmassS
  let f : Frame D k s₀ U' := { f₀ with i₀ := i₀, u₀ := u₀, core := C }
  let θ : ℝ := historyFloorFraction (D.K k) M m
  refine ⟨{
    frame := f
    θ := θ
    K₂ := D.N k ^ (ε / 2)
    steps := rfl
    good := ?_
    rho_floor := hCmass }, ?_⟩
  · refine {
      N_ge := p.scale k
      K_ge := hK1
      θ_pos := historyFloorFraction_pos hK hM1
      θ_le := historyFloorFraction_le_one hK1 hM1
      H_ge := hH1 k
      K₂_ge := Real.one_le_rpow (hN1 k) (by positivity)
      m_pos := hm
      U'_pos := hU'
      d_nonneg := p.dimension_nonneg
      κ_pos := p.rate_pos
      ℓ_eq := h.equal_rates
      depth_zero := by simp [Frame.depth, frameDepth]
      count := fun r _ => ⟨(grid r).1, (grid r).2.1⟩
      meas := fun r _ => (grid r).2.2.1
      disj := fun r _ => (grid r).2.2.2.1
      floor := fun r _ i => ((grid r).2.2.2.2.1 i).1
      ceil := fun r _ i => ((grid r).2.2.2.2.1 i).2.1
      cbound := fun r _ i => ((grid r).2.2.2.2.1 i).2.2.2.1
      rows := fun r _ i => ((grid r).2.2.2.2.1 i).2.2.2.2.2.1
      joint := ?_
      centered := ?_
      bmeas := hb
      νprob := hν
      dom := hdom
      anc_sub := fun r _ => hanc r
      core_meas := hCm
      core_nonempty := hCne
      core_parent_event := hCparent
      core_cover := hCcover
      core_inside := fun r hr i u hne => ⟨(hCfloor r hr i u hne).1, (hCfloor r hr i u hne).2.1⟩
      core_floor := fun r hr i u hne => ((hCfloor r hr i u hne).2.2).trans (hρ _)
      contact := ?_ }
    · intro r _ i v v₀ hv hv'
      exact (grid r).2.2.2.2.2.2 i v v₀ (hRkinv.trans hv) (hv'.trans hRk)
    · intro r _ i
      have hc := hkcenter (depth r) (hRinv.trans (hdepth r).1) (hdepthU r)
        ((mul_le_mul_of_nonneg_left (hdepth r).2 p.rate_pos.le).trans hmargin) i
      simpa only [Frame.mid, Frame.ql, Frame.Tl, Frame.depth, frameDepth, f, f₀,
        depth, finiteGridDepth, zpow_neg, zpow_natCast] using hc
    · intro x hx
      have hdx : |D.b k x.1 4 + D.b k x.1 0| ≤ D.N k ^ (-D.e₀) := hCcontact x hx
      have hd0 : f.depth 0 = s₀ := by simp [Frame.depth, frameDepth]
      have hqinv : f.q₀⁻¹ = (2 : ℝ) ^ D.T k s₀ := by
        change (((2 : ℝ) ^ D.T k (f.depth 0))⁻¹)⁻¹ = _
        rw [inv_inv, hd0]
      have hTup : (2 : ℝ) ^ D.T k s₀ ≤ D.K k * D.N k ^ (D.κ * s₀) := by
        simpa only [depth, finiteGridDepth_zero] using (grid 0).2.1
      rw [div_eq_mul_inv, hqinv]
      calc
        _ ≤ D.N k ^ (-D.e₀) * (2 : ℝ) ^ D.T k s₀ :=
          mul_le_mul_of_nonneg_right hdx (by positivity)
        _ ≤ D.N k ^ (-D.e₀) * (D.K k * D.N k ^ (D.κ * s₀)) :=
          mul_le_mul_of_nonneg_left hTup (Real.rpow_nonneg hN.le _)
        _ ≤ D.N k ^ (-D.e₀) * (D.N k ^ e' * D.N k ^ (D.κ * s₀)) := by
          gcongr
        _ = D.N k ^ (-e') := by
          rw [← Real.rpow_add hN, ← Real.rpow_add hN]
          congr 1
          dsimp only [e']
          ring
  · exact hkcost M hMbound

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
