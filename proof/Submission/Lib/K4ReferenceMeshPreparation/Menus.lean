/-
Adapted from: here:o107 (session x0735), original-reference cap and
two-scale record helpers in Submission/Obl/k4_finite_narrowness_path_improvement/.
Accepted history-floor and mesh-cover proofs are imported.
-/
import Submission.Lib.K4ReferenceMeshPreparation.NativeCaps
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-! Finite native cell menus from anisotropic base/signal diameter bounds.
The box covers and same-cell metric estimate are imported from accepted
modules; no absolute hidden-coordinate or coefficient bound is used. -/

namespace Submission.Lib.K4ReferenceMeshPreparation

noncomputable section

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open Submission.Lib.K4MovingMeshBoxes

private theorem mesh_bin_distance {a x y : ℝ} (ha : 0 < a)
    (h : ⌊x/a⌋ = ⌊y/a⌋) : |x-y| ≤ a := by
  have hd := (Int.abs_sub_lt_one_of_floor_eq_floor h).le
  rw [← sub_div,abs_div,abs_of_pos ha,div_le_iff₀ ha] at hd
  simpa only [one_mul] using hd

/-- An anisotropic three-base/one-signal box meets polynomially many
native cells, with different base and signal resolutions. -/
theorem native_signal_box_menu {ε a L : ℝ} (hε : 0 < ε) (ha : 0 < a) (hL : 0 ≤ L)
    (center : Fin 3 → ℝ) (signalCenter : ℝ) :
    ∃ F : Finset NativeSignalCell, (F.card : ℝ) ≤ (4*L+2)^4 ∧
      ∀ (y : Fin 3 → ℝ) (z : ℝ), (∀ i, |y i-center i| ≤ L*ε) →
        |z-signalCenter| ≤ L*a →
        (Submission.Lib.K4AffineMeshCaps.baseMesh ε y,⌊z/a⌋) ∈ F := by
  classical
  let c : Fin 2 → ℝ := ![center 1,center 2]
  obtain ⟨B,hB,hBc⟩ := movingBox_mesh_cover hε (mul_nonneg hL hε.le) (by norm_num : (0 : ℝ) ≤ 0)
    (center 0) c 0 (fun _ => L*ε) (by simp) (fun _ => mul_nonneg hL hε.le)
  have hB' : (B.card : ℝ) ≤ (4*L+2)^3 := by
    convert hB using 1
    simp only [zero_mul,add_zero,Fin.prod_univ_two]
    field_simp [hε.ne']
  obtain ⟨D,hD,hDc⟩ := interval_mesh_cover ha (mul_nonneg hL ha.le) signalCenter
  have hD' : (D.card : ℝ) ≤ 4*L+2 := by
    convert hD using 1
    field_simp [ha.ne']
  refine ⟨B.product D,?_,?_⟩
  · calc
      ((B.product D).card : ℝ) = (B.card : ℝ)*(D.card : ℝ) := by simp
      _ ≤ (4*L+2)^3*(4*L+2) := mul_le_mul hB' hD' (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  · intro y z hy hz
    have hybox : y ∈ movingBox (center 0) (L*ε) c 0 (fun _ => L*ε) := by
      refine ⟨hy 0,?_⟩
      intro i
      fin_cases i
      · simpa [c] using hy 1
      · simpa [c] using hy 2
    exact Finset.mem_product.mpr ⟨hBc y hybox,hDc z hz⟩

/-- Uniform base/signal diameters produce the finite options and padded
cell menus needed by the original-reference cap constructor. The menu
sizes depend only on the diameter constant, not on the record count or
on the position of any record. -/
theorem native_record_cell_menus {Ω ι : Type*}
    (N r s L : ℝ) (hN : 0 < N) (hL : 0 ≤ L)
    (x : Ω → Fin 4 → ℝ) (P : MvPolynomial (Fin 4) ℝ) (H : ι → Set Ω)
    (hdiam : ∀ i p, p ∈ H i → ∀ p', p' ∈ H i →
      (∀ j : Fin 3, |x p j.castSucc-x p' j.castSucc| ≤ L*N^(-r)) ∧
        |eval (x p) P-eval (x p') P| ≤ L*N^(-s)) :
    ∃ (options : ι → Finset NativeSignalCell) (padding : NativeSignalCell → Finset NativeSignalCell),
      (∀ i, ((options i).card : ℝ) ≤ (4*L+2)^4) ∧
      (∀ q, ((padding q).card : ℝ) ≤ (4*L+6)^4) ∧
      (∀ i p, p ∈ H i → nativeSignalCell N r s x P p ∈ options i) ∧
      (∀ i q, q ∈ options i → ∃ p ∈ H i, nativeSignalCell N r s x P p = q) ∧
      (∀ i q, q ∈ options i → ∀ p ∈ H i, nativeSignalCell N r s x P p ∈ padding q) := by
  classical
  let ε := N^(-r)
  let a := N^(-s)
  have hε : 0 < ε := Real.rpow_pos_of_pos hN _
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  let state := nativeSignalCell N r s x P
  have hopt (i : ι) : ∃ F : Finset NativeSignalCell,
      (F.card : ℝ) ≤ (4*L+2)^4 ∧
        (∀ p ∈ H i, state p ∈ F) ∧ (∀ q ∈ F, ∃ p ∈ H i, state p = q) := by
    by_cases hi : (H i).Nonempty
    · obtain ⟨p₀,hp₀⟩ := hi
      obtain ⟨G,hG,hGc⟩ := native_signal_box_menu hε ha hL
        (fun j : Fin 3 => x p₀ j.castSucc) (eval (x p₀) P)
      let F := G.filter (fun q => ∃ p ∈ H i, state p = q)
      have hcard : F.card ≤ G.card := Finset.card_filter_le _ _
      refine ⟨F,(show (F.card : ℝ) ≤ G.card by exact_mod_cast hcard).trans hG,?_,?_⟩
      · intro p hp
        exact Finset.mem_filter.mpr ⟨hGc _ _ (hdiam i p hp p₀ hp₀).1
          (hdiam i p hp p₀ hp₀).2,p,hp,rfl⟩
      · intro q hq
        exact (Finset.mem_filter.mp hq).2
    · refine ⟨∅,?_,?_,?_⟩
      · simpa using (show (0 : ℝ) ≤ (4*L+2)^4 by positivity)
      · intro p hp
        exact (hi ⟨p,hp⟩).elim
      · intro q hq
        simp at hq
  choose options hoptions using hopt
  have hpad (q : NativeSignalCell) : ∃ G : Finset NativeSignalCell,
      (G.card : ℝ) ≤ (4*L+6)^4 ∧
        ∀ i, q ∈ options i → ∀ p ∈ H i, state p ∈ G := by
    by_cases hq : ∃ p : Ω, state p = q
    · obtain ⟨p₁,hp₁⟩ := hq
      obtain ⟨G,hG,hGc⟩ := native_signal_box_menu hε ha (by linarith : 0 ≤ L+1)
        (fun j : Fin 3 => x p₁ j.castSucc) (eval (x p₁) P)
      refine ⟨G,hG.trans_eq (by congr 1; ring),?_⟩
      intro i hi p hp
      obtain ⟨p₀,hp₀,hp₀q⟩ := (hoptions i).2.2 q hi
      have heq : state p₀ = state p₁ := hp₀q.trans hp₁.symm
      have hbase (j : Fin 3) : |x p j.castSucc-x p₁ j.castSucc| ≤ (L+1)*ε := by
        have hcode : ⌊x p₀ j.castSucc/ε⌋ = ⌊x p₁ j.castSucc/ε⌋ :=
          congrFun (congrArg Prod.fst heq) j
        have hd := mesh_bin_distance hε hcode
        calc
          _ = |(x p j.castSucc-x p₀ j.castSucc)+(x p₀ j.castSucc-x p₁ j.castSucc)| := by
            congr 1
            ring
          _ ≤ |x p j.castSucc-x p₀ j.castSucc|+|x p₀ j.castSucc-x p₁ j.castSucc| := abs_add_le _ _
          _ ≤ L*ε+ε := add_le_add ((hdiam i p hp p₀ hp₀).1 j) hd
          _ = _ := by ring
      have hsignal : |eval (x p) P-eval (x p₁) P| ≤ (L+1)*a := by
        have hcode : ⌊eval (x p₀) P/a⌋ = ⌊eval (x p₁) P/a⌋ := congrArg Prod.snd heq
        have hd := mesh_bin_distance ha hcode
        calc
          _ = |(eval (x p) P-eval (x p₀) P)+(eval (x p₀) P-eval (x p₁) P)| := by
            congr 1
            ring
          _ ≤ |eval (x p) P-eval (x p₀) P|+|eval (x p₀) P-eval (x p₁) P| := abs_add_le _ _
          _ ≤ L*a+a := add_le_add (hdiam i p hp p₀ hp₀).2 hd
          _ = _ := by ring
      exact hGc _ _ hbase hsignal
    · refine ⟨∅,?_,?_⟩
      · simpa using (show (0 : ℝ) ≤ (4*L+6)^4 by positivity)
      · intro i hi p hp
        obtain ⟨p₀,hp₀,hp₀q⟩ := (hoptions i).2.2 q hi
        exact (hq ⟨p₀,hp₀q⟩).elim
  choose padding hpadding using hpad
  exact ⟨options,padding,fun i => (hoptions i).1,fun q => (hpadding q).1,
    fun i => (hoptions i).2.1,fun i => (hoptions i).2.2,
    fun i q hq => (hpadding q).2 i hq⟩

/-- One finest-scale diameter bound assembles all native E2 fields on
the whole requested range, using a polynomial padding budget. All history
weights and velocity-palette factors remain their original ones. -/
theorem native_cell_caps_of_record_diameters
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (N K C d S R L : ℝ) (hN : 1 < N) (hK : 0 ≤ K) (hC : 1 ≤ C) (hL : 0 ≤ L)
    (ν μ : Measure Ω) (hμ : μ ≤ ν) (π : Measure ℝ)
    (x : Ω → Fin 4 → ℝ) (hx : Measurable x) (P : MvPolynomial (Fin 4) ℝ)
    (velocity : Ω → ℝ)
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : Pairwise (fun i j => AEDisjoint ν (H i) (H j)))
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≤ ν (H i))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ H i)
    (hdiam : ∀ i p, p ∈ H i → ∀ p', p' ∈ H i →
      (∀ j : Fin 3, |x p j.castSucc-x p' j.castSucc| ≤ L*N^(-R)) ∧
        |eval (x p) P-eval (x p') P| ≤ L*N^(-R))
    (hpure : ∀ r s, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
      ∀ q, ν {p | nativeSignalCell N r s x P p = q} ≤ ENNReal.ofReal (K*N^(-3*r-d*s)))
    (hpalette : ∀ v, R⁻¹ ≤ v → v ≤ R → ∀ z : ℤ,
      π {t | ⌊t/N^(-v)⌋ = z} ≤ ENNReal.ofReal (K*N^(-S*v)))
    (hrecord : ∀ v, R⁻¹ ≤ v → v ≤ R → ∀ i z,
      μ (H i ∩ {p | ⌊velocity p/N^(-v)⌋ = z}) ≤
        ENNReal.ofReal C*w i*π {t | ⌊t/N^(-v)⌋ = z}) :
    NativeCellCaps N (C*(Nat.ceil ((4*L+6)^4) : ℝ)*K) d S R μ π x P velocity := by
  classical
  let M := Nat.ceil ((4*L+6)^4)
  have hM : 1 ≤ M := Nat.ceil_pos.mpr (pow_pos (by linarith : 0 < 4*L+6) 4)
  have hN0 : 0 < N := by linarith
  have hmenus (r s : ℝ) :
      ∃ (options : ι → Finset NativeSignalCell) (padding : NativeSignalCell → Finset NativeSignalCell),
        (r ≤ R ∧ s ≤ R) →
          (∀ q, (padding q).card ≤ M) ∧
          (∀ i p, p ∈ H i → nativeSignalCell N r s x P p ∈ options i) ∧
          (∀ i q, q ∈ options i → ∀ p ∈ H i, nativeSignalCell N r s x P p ∈ padding q) := by
    by_cases hrs : r ≤ R ∧ s ≤ R
    · have hbase : N^(-R) ≤ N^(-r) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by linarith [hrs.1])
      have hsignal : N^(-R) ≤ N^(-s) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by linarith [hrs.2])
      have hdiam' : ∀ i p, p ∈ H i → ∀ p', p' ∈ H i →
          (∀ j : Fin 3, |x p j.castSucc-x p' j.castSucc| ≤ L*N^(-r)) ∧
            |eval (x p) P-eval (x p') P| ≤ L*N^(-s) := by
        intro i p hp p' hp'
        obtain ⟨hb,hs⟩ := hdiam i p hp p' hp'
        exact ⟨fun j => (hb j).trans (mul_le_mul_of_nonneg_left hbase hL),
          hs.trans (mul_le_mul_of_nonneg_left hsignal hL)⟩
      obtain ⟨options,padding,hopt,hpad,hcover',hsupport,hlocal⟩ :=
        native_record_cell_menus N r s L hN0 hL x P H hdiam'
      have hcount (q : NativeSignalCell) : (padding q).card ≤ M := by
        have hc : ((padding q).card : ℝ) ≤ M := (hpad q).trans (Nat.le_ceil _)
        exact_mod_cast hc
      exact ⟨options,padding,fun _ => ⟨hcount,hcover',hlocal⟩⟩
    · exact ⟨fun _ => ∅,fun _ => ∅,fun h => (hrs h).elim⟩
  choose options padding hmenus using hmenus
  exact native_cell_caps_of_localized_records N K C d S R hN0 hK hC M hM ν μ hμ π x hx P velocity
    H hH hdisj w hw options padding hcover
    (fun r s hrl hrh hs0 hsh i =>
      Filter.Eventually.of_forall (fun p hp => (hmenus r s ⟨hrh,hsh⟩).2.1 i p hp))
    (fun r s hrl hrh hs0 hsh i q hq =>
      Filter.Eventually.of_forall (fun p hp => (hmenus r s ⟨hrh,hsh⟩).2.2 i q hq p hp))
    (fun r s hrl hrh hs0 hsh => (hmenus r s ⟨hrh,hsh⟩).1) hpure hpalette hrecord

end

end Submission.Lib.K4ReferenceMeshPreparation
