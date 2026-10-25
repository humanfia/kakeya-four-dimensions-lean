-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.VolumeRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinedCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AngularFilling
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismBridge
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.LocalToGlobal
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GlobalFilling
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularShading
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularPrism
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ScaleDyadic
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AngularAnnuli
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ThinNeighborhood
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SquareRootPacking
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.EnlargedBodies
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeStretch
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeEnlargement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityClasses
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodAverage
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodTransfer
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarsePrism
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AxisBounds
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GridPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketNormalization
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketContainment
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AngularPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SpatialPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GeometricPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SubfamilyRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinedRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensePacketAssembly
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NarrowRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineFillingDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodGain
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseAffine
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NormalizedGrains
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BadIncidences
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TransverseDichotomy
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ThickGrainDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseDichotomy
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinedDichotomy
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FiberAssembly
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainRotation
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CommonCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallPowers
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.NearRoundCover
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FineCoverEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.GroupedMultiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityPower
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinementPowers
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainScales
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.MediumPowers
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainCardinality
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainCoverEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.MediumEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CrossScaleCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Proof
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_clustered_cover_volume_gain`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_clustered_cover_volume_gain/`
belong to this obligation.
-/

theorem WangZahlLot.wz_clustered_cover_volume_gain : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∀B,B=(fun(d ρ l:ℝ)(n N:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(y w:Fin N→V)(f:Fin n→Fin N)=>∀k,(fun(D:Set V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|i∈S∧f i=k∧T d (x i) (v i)⊆D∩Q u t r})*μ D≤O (l*q n {i|i∈S∧f i=k})*μ (D∩Q u t r)) (T (2*ρ) (y k-(1/2:ℝ)•w k) (2•w k)))→∀C,C=(fun(d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>(∀i,M (Z i)∧Z i⊆Y i∧(i∉S→Z i=∅))∧O (d^h)*∑i,μ (Y i)≤∑i∈S,μ (Z i)∧(∀k,‖w k‖=1)∧(∀i∈S,T d (x i) (v i)⊆T ρ (y (f i)) (w (f i)))∧F ρ (d^(-h)) N y w∧B d ρ (d^(-h)) n N x v S y w f∧(∀k k',q n {i|i∈S∧f i=k}≤d^(-h)*q n {i|i∈S∧f i=k'})∧X ρ N y w∧∀i∈S,q N {k|T d (x i) (v i)⊆T ρ (y k) (w k)}≤d^(-h))→∀G,G=(fun(ω d h:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)=>C d h n x v Y S Z ρ N y w f∧d^(1-ω/100)≤ρ∧ρ≤d^(ω/100)∧∃(a c:ℝ)(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),(fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧d^h*(ρ/d)*N/n≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O (d^(-h))*μ W) (fun j=>P a (ρ*c) c (z j) (e j)))→∀E,E=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃a:ℝ,0<a∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀m l:ℝ,1≤ m→1≤l→∀n x v Y,A δ η m l n x v Y→O (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*l*(n*δ))^(-σ))≤μ (⋃i,Y i))→∀J,J=(fun(σ ω:ℝ)=>∀ε:ℝ,0<ε→∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ:ℝ,δ≤ρ→ρ≤1→∀N y w f,C δ η n x v Y .univ Y ρ N y w f→∀a b c:ℝ,ρ≤a→a≤b→b≤c→1≤c→c≤8→∀(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(g:Fin N→Fin L),(fun(U:Fin L→Set V)=>(∀k,T ρ (y k) (w k)⊆U (g k))→(∀j j',q N {k|g k=j}≤δ^(-η)*q N {k|g k=j'})→(∀k,q L {j|T ρ (y k) (w k)⊆U j}≤δ^(-η))→(∀W,Convex ℝ W→O (q L {j|U j⊆W}*(a*b*c))≤O (δ^(-η))*μ W)→(∀j W,Convex ℝ W→O (q N {k|g k=j∧T ρ (y k) (w k)⊆U j∩W})*μ (U j)≤O (δ^(-η)*q N {k|g k=j})*μ (U j∩W))→O (κ*δ^(ω+ε)*(b/a)^ω*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)) (fun j=>P a b c (z j) (e j)))→E σ ω→J σ ω→∀ζ:ℝ,0<ζ→∃h:ℝ,0<h∧h≤ζ/10∧∃α:ℝ,0<α∧∃κ:ℝ,0<κ∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ h (δ^(-h)) (δ^(-h)) n x v Y→∀S Z ρ N y w f,G ω δ h n x v Y S Z ρ N y w f→(∀U:Finset (Fin N),O (δ^(ζ/2))*∑i∈S,μ (Z i)≤∑i∈S.filter (fun i=>f i∈U),μ (Z i)→¬∀W,Convex ℝ W→O (q N {k|k∈U∧T ρ (y k) (w k)⊆W}*ρ^2)≤O (δ^(-ζ))*μ W)→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσhalf hω hω1
  dsimp only
  rintro O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl P rfl B rfl C rfl
    G rfl E rfl J rfl hE hJ ζ hζ
  exact WangZahlLot.Obl.wz_clustered_cover_volume_gain.clustered_gain hσ hσhalf hω hω1 hE hJ hζ
