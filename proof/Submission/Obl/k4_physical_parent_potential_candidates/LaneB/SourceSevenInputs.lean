import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceEventTubes

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData

noncomputable section

namespace SourceNormalization

def eventBase (T j:ℕ) (c u:P2) (s:ℝ) (b cz:Fin 3 → ℝ) (lam B:ℝ) (e:Ev) : P3 :=
  Analytic.normalizedBase (Analytic.zoomForwardShift (shift T j c u s b) cz lam)
    (lam • matrix T s) B (Analytic.graphPoint e.1 e.2)

theorem zoomed_state_distance {q T j:ℕ} {ν:Measure Ln} {B a ζ d:ℝ} {c u:P2} {P0:Po}
    {A:Set Ln} {F H:Set Ev} (source:PhysicalSource q ν B a ζ d T j c u P0 A F H)
    {s lam:ℝ} (hs:0<s) (hlam:0<lam) (b cz:Fin 3 → ℝ) {e f:Ev}
    (hcode:source.fineState e=source.fineState f) :
    ‖eventBase T j c u s b cz lam B e-eventBase T j c u s b cz lam B f‖ ≤ 3*lam*source.ε/s := by
  unfold eventBase
  rw [Analytic.normalizedBase_zoom,Analytic.normalizedBase_zoom]
  have heq : Analytic.zoomMap (WithLp.toLp 2 cz) lam
      (Analytic.normalizedBase (shift T j c u s b) (matrix T s) B (Analytic.graphPoint e.1 e.2))-
      Analytic.zoomMap (WithLp.toLp 2 cz) lam
      (Analytic.normalizedBase (shift T j c u s b) (matrix T s) B (Analytic.graphPoint f.1 f.2)) =
      lam • (Analytic.normalizedBase (shift T j c u s b) (matrix T s) B (Analytic.graphPoint e.1 e.2)-
        Analytic.normalizedBase (shift T j c u s b) (matrix T s) B (Analytic.graphPoint f.1 f.2)) := by
    ext i
    simp [Analytic.zoomMap]
    ring
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos hlam]
  have hh := normalized_state_distance source hs b hcode
  calc _ ≤ lam*(3*source.ε/s) := mul_le_mul_of_nonneg_left hh hlam.le
    _ = _ := by ring

/-- Original per-state breadth yields all seven actual tube and potential
jet witnesses needed by normalized restoration, at every later localized
anchor. Only null original states are removed; witnesses are sampled from
the original prelocalization group. -/
theorem exists_seven_tube_core (q:ℕ) (hq:2≤q) :
    ∃ Cq:ℝ, 0<Cq ∧ ∀ {T j:ℕ} {ν:Measure Ln} [IsFiniteMeasure ν]
      {B a ζ d:ℝ} {c u:P2} {P0:Po} {A:Set Ln} {F H:Set Ev}
      (source:PhysicalSource q ν B a ζ d T j c u P0 A F H), P0.totalDegree≤2 → 0<B →
      source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
        ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹) →
    ∀ G:Set Ev, MeasurableSet G → G ⊆ source.positiveEvents →
      (∀ L:Set ((Fin 3 → ℤ) × ℤ), ∀ n:P2, ∀ t:ℝ, ‖n‖=1 →
        ((ν.prod volume).restrict G)
          {e | source.fineState e∈L ∧ |inner ℝ n (v e.1)-t| ≤ source.K^(-100:ℝ)} ≤
        ENNReal.ofReal ((1:ℝ)/1000000)*
          ((ν.prod volume).restrict G) {e | source.fineState e∈L}) →
    ∃ U:Set Ev, MeasurableSet U ∧ U ⊆ G ∧
      (ν.prod volume).restrict U=(ν.prod volume).restrict G ∧
    ∀ {s lam At τw hδ εfit A₁ σ Vc c0:ℝ}, 0<s → 1≤lam →
      1+2*source.K≤At → At⁻¹≤(source.K^(-100:ℝ))^2 →
      0≤hδ → 3*lam*source.ε/s≤hδ → hδ≤1/2 →
      scale T s/(8*At*lam)≤τw →
    ∀ (b cz:Fin 3 → ℝ) (Rc:Po),
      (∀ e∈G,∀t:ℝ,|t-e.2|≤τw →
        Analytic.PhysicalGroupPoint B⁻¹ (P0-C c0) Rc
          (Broad.parentPotentialPullback T j c u source.Pot) εfit A₁ σ Vc (Analytic.graphPoint e.1 t)) →
    ∀ x∈U, ‖eventBase T j c u s b cz lam B x‖<1/2 →
    ∃ p y:Fin 7 → P3,
      (∀ i,p i 0=1 ∧ ‖p i‖≤At) ∧
      (∀ i j k:Fin 7,i≠j → i≠k → j≠k →
        At⁻¹≤|Matrix.det (Matrix.of fun r t:Fin 3 => (![p i,p j,p k] r) t)|) ∧
      (∀ i,Analytic.CertifiedTubeWitness
        (Analytic.transportPolynomial (Analytic.zoomShift (inverseShift T j c u s b)
          (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam) B⁻¹ (P0-C c0))
        (zoomPotential T j c u s b cz lam source.Pot)
        (Analytic.transportPolynomial (Analytic.zoomShift (inverseShift T j c u s b)
          (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam) B⁻¹ Rc)
        εfit A₁ σ Vc At 1 hδ (eventBase T j c u s b cz lam B x) (p i)) ∧
      (∀ i, ‖y i‖≤1 ∧ ‖eventBase T j c u s b cz lam B x-y i‖≤hδ ∧
        |iteratedFDeriv ℝ 3
          (fun z:P3 => eval (fun j => z j) (zoomPotential T j c u s b cz lam source.Pot))
          (y i) (fun _ => p i)| ≤ Cq*s^3*a*ζ) := by
  obtain ⟨Cq,hCq,hjets⟩ := exists_uniform_zoomed_source_jet_bound q hq 3 (by decide)
  refine ⟨Cq,hCq,?_⟩
  intro T j ν _ B a ζ d c u P0 A F H source hP0 hB hSA G hG hGpos hbroad
  have hGS : G ⊆ source.S := hGpos.trans source.positive_events_subset
  have hraw := original_block_mass_le ν A ((j:ℝ)*((2:ℝ)^T)⁻¹) ((2:ℝ)^T)⁻¹ G (hGS.trans hSA)
  rw [Measure.restrict_apply_univ] at hraw
  have hGfin : (ν.prod volume) G≠⊤ := ne_top_of_le_ne_top (by finiteness) hraw
  obtain ⟨U,hU,hUG,hlaw,hseven⟩ := source.seven_event_core G hG hGS hGfin hbroad
  refine ⟨U,hU,hUG,hlaw,?_⟩
  intro s lam At τw hδ εfit A₁ σ Vc c0 hs hlam hAtv hDet hhδ hmesh hhδhalf hwindow
    b cz Rc hphys x hx hxhalf
  have hLamPos : 0<lam := by linarith
  have hAt : 1≤At := by linarith [source.K_two]
  obtain ⟨e,he,hdet⟩ := hseven x hx
  let p:Fin 7 → P3 := fun i => Analytic.GeneralPositionSampling.lift (v (e i).1)
  let y:Fin 7 → P3 := fun i => eventBase T j c u s b cz lam B (e i)
  have hxy (i:Fin 7) : ‖eventBase T j c u s b cz lam B x-y i‖≤hδ := by
    rw [norm_sub_rev]
    exact (zoomed_state_distance source hs hLamPos b cz (he i).2.1).trans hmesh
  have hy (i:Fin 7) : ‖y i‖≤1 := by
    have htri : ‖y i‖≤‖y i-eventBase T j c u s b cz lam B x‖+
        ‖eventBase T j c u s b cz lam B x‖ := by
      convert norm_add_le (y i-eventBase T j c u s b cz lam B x)
        (eventBase T j c u s b cz lam B x) using 1 <;> simp
    have hnear := hxy i
    rw [norm_sub_rev] at hnear
    linarith
  refine ⟨p,y,?_,?_,?_,?_⟩
  · intro i
    exact ⟨rfl,(he i).2.2.2.trans hAtv⟩
  · intro i j k hij hik hjk
    exact hDet.trans (hdet i j k hij hik hjk)
  · intro i
    apply certified_tube_of_physical_window T j c u hs hLamPos hB b cz
      (P0-C c0) Rc (Broad.parentPotentialPullback T j c u source.Pot) (e i) hAt
      (source.point_bounds (e i) (hGS (he i).1)).2.1 hAtv hhδ hwindow
      (hphys (e i) (he i).1) ?_ (eventBase T j c u s b cz lam B x) (hxy i)
    simpa only [y,eventBase,Metric.mem_closedBall,dist_zero_right] using hy i
  · intro i
    have htime : (e i).2∈Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹) := by
      simpa only [add_mul,one_mul] using (hSA (hGS (he i).1)).2
    refine ⟨hy i,hxy i,?_⟩
    exact hjets source hP0 hs b cz hlam (e i).1 (hGpos (he i).1).2 (e i).2 htime (y i)
      (zoomPotential_point T j c u hs b cz hLamPos.ne' B (e i))

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
