import Mathlib

variable {R : Type} [CommRing R]
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

section noncategorical

variable {M : Type} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [Module R M] [ContinuousConstSMul R M]
variable {M' : Type} [TopologicalSpace M'] [AddCommGroup M'] [IsTopologicalAddGroup M'] [Module R M'] [ContinuousConstSMul R M']
variable {M'' : Type} [TopologicalSpace M''] [AddCommGroup M''] [IsTopologicalAddGroup M''] [Module R M''] [ContinuousConstSMul R M'']
variable (π : Representation R G M) (π' : Representation R G M') (π'' : Representation R G M'')

-- TODO : generalize this and move to a more suitable file.
instance (N : Submodule R M) : ContinuousConstSMul R N where
  continuous_const_smul r := by
    apply Continuous.subtype_map
    · exact ContinuousConstSMul.continuous_const_smul r
    · exact fun n hn ↦ Submodule.smul_mem N r hn

class WeaklyContinuous : Prop where
  is_continuous (g : G) : Continuous (fun m : M ↦ π g m)

variable [WeaklyContinuous π] [WeaklyContinuous π'][WeaklyContinuous π'']

def IsTopologicalGroup.left_mul (g : G) : C(G,G) := ⟨(g * ·), continuous_mul_left g⟩

lemma IsTopologicalGroup.left_mul_apply (g : G) (x : G) : left_mul g x = g * x := rfl

namespace WeaklyContinuous
open IsTopologicalGroup

def I : Representation R G C(G,M) where
  toFun g           := {
    toFun f         := ContinuousMap.comp ⟨(π g),WeaklyContinuous.is_continuous g⟩ (ContinuousMap.comp f ⟨fun x ↦ g⁻¹ * x, continuous_mul_left g⁻¹⟩)
    map_add' _ _    := by ext; simp
    map_smul' _ _   := by ext; simp
  }
  map_one' := by ext; simp
  map_mul' g₁ g₂ := by ext; simp [mul_assoc]

lemma I_apply₄ (g : G) (f : C(G,M)) (x : G) : I π g f x = π g (f (g⁻¹ * x)) := rfl
lemma I_apply₃ (g : G) (f : C(G,M)) : I π g f = ContinuousMap.comp ⟨(π g), WeaklyContinuous.is_continuous g⟩ (f.comp (left_mul g⁻¹)) := rfl

instance : ContinuousConstSMul R C(G,M) where
  continuous_const_smul r := by
    rw [ContinuousMap.continuous_compactOpen]
    intro K hK U hU
    exact ContinuousMap.isOpen_setOf_mapsTo hK ((ContinuousConstSMul.continuous_const_smul (T := M) r).isOpen_preimage U hU)

instance I_weaklyContinuous : WeaklyContinuous (I π) where
  is_continuous g := by
    rw [ContinuousMap.continuous_compactOpen]
    intro K hK U hU
    let K' := (left_mul g⁻¹) '' K
    let U' := (π g) ⁻¹' U
    have : IsOpen {f : C(G,M) | Set.MapsTo f K' U'}
    · apply ContinuousMap.isOpen_setOf_mapsTo
      · exact IsCompact.image hK (ContinuousMap.continuous (left_mul g⁻¹))
      · exact Continuous.isOpen_preimage (WeaklyContinuous.is_continuous g) U hU
    have : {f : C(G,M) | Set.MapsTo f K' U'} = {f | Set.MapsTo (I π g f) K U}
    · ext f
      simp [Set.mapsTo_iff_subset_preimage]
      constructor
      · intro hf x hx
        rw [Set.mem_preimage, I_apply₄, ←Set.mem_preimage]
        apply hf
        rw [Set.mem_image]
        use x, hx
        exact left_mul_apply g⁻¹ x
      · intro hf x hx
        have : g * x ∈ (I π g f) ⁻¹' U
        · apply hf
          rw [Set.mem_image] at hx
          obtain ⟨k, hk, rfl⟩ := hx
          rwa [left_mul_apply, ←mul_assoc, mul_inv_cancel, one_mul]
        rwa [Set.mem_preimage, I_apply₄, ←mul_assoc, inv_mul_cancel, one_mul,←Set.mem_preimage,←Set.mem_preimage] at this
    rwa [←this]

end WeaklyContinuous
open WeaklyContinuous

def continuousIntertwining : Submodule R (M →L[R] M') := {
  carrier := {φ : M →L[R] M' | ∀ g : G, ∀ m : M, φ ((π g) m) = (π' g) (φ m)}
  zero_mem' := by simp
  add_mem' hφ hψ _ _   := by rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add, hφ, hψ]
  smul_mem' _ _ hφ _ _ := by rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply, map_smul, hφ]
}

def ContinuousIntertwining : Type := continuousIntertwining π π'
notation π " →ᵢ " π' => ContinuousIntertwining π π'

instance : AddCommGroup (π →ᵢ π') := inferInstanceAs (AddCommGroup (continuousIntertwining π π'))
instance : Module R (π →ᵢ π') := inferInstanceAs (Module R (continuousIntertwining π π'))

namespace ContinuousIntertwining

omit [TopologicalSpace G] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [WeaklyContinuous π] [WeaklyContinuous π'] in
@[ext] lemma ext (φ ψ : π →ᵢ π') (h : φ.val = ψ.val) : φ = ψ := Subtype.ext h

instance : FunLike (π →ᵢ π') M M' where
  coe φ := φ.val
  coe_injective' _ _ h := ext (h := ContinuousLinearMap.ext (congrFun h))

instance : AddHomClass (π →ᵢ π') M M' := ⟨fun φ ↦ map_add φ.val⟩
instance : MulActionHomClass (π →ᵢ π') R M M' := ⟨fun φ ↦ map_smul φ.val⟩

def id : π →ᵢ π where
  val           := ContinuousLinearMap.id R M
  property _ _  := rfl

omit [TopologicalSpace G] [WeaklyContinuous π] in
@[simp] lemma id_apply (m : M) : id π m = m := rfl

section omit_instance
variable {π π' π''}
omit [TopologicalSpace G] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [WeaklyContinuous π] [WeaklyContinuous π'] [WeaklyContinuous π'']

@[norm_cast] lemma coe_apply (φ : π →ᵢ π') (m : M) : φ.val m = φ m := rfl
@[push_cast] lemma coe_add (φ ψ : π →ᵢ π') : (φ + ψ).val = φ.val + ψ.val := rfl
@[push_cast] lemma coe_sub (φ ψ : π →ᵢ π') : (φ - ψ).val = φ.val - ψ.val := rfl
@[push_cast] lemma coe_smul (r : R) (φ : π →ᵢ π') : (r • φ).val = r • φ.val := rfl

@[simp] lemma zero_apply (m : M) : (0 : π →ᵢ π') m = 0 := rfl
@[simp] lemma add_apply (φ ψ : π →ᵢ π') (m : M) : (φ + ψ) m = φ m + ψ m := rfl
@[simp] lemma sub_apply (φ ψ : π →ᵢ π') (m : M) : (φ - ψ) m = φ m - ψ m := rfl
@[simp] lemma smul_apply (r : R) (φ : π →ᵢ π') (m : M) : (r • φ) m = r • (φ m) := rfl
@[simp] lemma comm (φ : π →ᵢ π') (g : G) (m : M) : φ (π g m) = π' g (φ m) := φ.property g m

lemma comm' (φ : π →ᵢ π') (g : G) : φ ∘ π g = π' g ∘ φ := by ext; simp

def compᵢ (φ : π' →ᵢ π'') (ψ : π →ᵢ π') : (π →ᵢ π'') where
  val           := φ.val ∘L ψ.val
  property _ _  := by simp [coe_apply]

notation3:80 (name := compNotation) φ:81 " ∘ᵢ " ψ:80 => compᵢ φ ψ

@[simp] lemma id_comp (φ : π →ᵢ π') : id π' ∘ᵢ φ = φ := rfl

@[push_cast] lemma coe_compᵢ (φ : π' →ᵢ π'') (ψ : π →ᵢ π') : (φ ∘ᵢ ψ).val = φ.val ∘L ψ.val := rfl

@[simp] lemma compᵢ_add (φ : π' →ᵢ π'') (ψ₁ ψ₂ : π →ᵢ π') : φ ∘ᵢ (ψ₁ + ψ₂) = φ ∘ᵢ ψ₁ + φ ∘ᵢ ψ₂ := by
  ext : 1
  push_cast
  simp

@[simp] lemma compᵢ_sub (φ : π' →ᵢ π'') (ψ₁ ψ₂ : π →ᵢ π') : φ ∘ᵢ (ψ₁ - ψ₂) = φ ∘ᵢ ψ₁ - φ ∘ᵢ ψ₂ := by
  ext : 1
  push_cast
  simp

@[simp] lemma compᵢ_smul (φ : π' →ᵢ π'') (r : R) (ψ : π →ᵢ π') : φ ∘ᵢ (r • ψ) = r • (φ ∘ᵢ ψ) := by
  ext : 1
  push_cast
  simp

@[simp] lemma add_compᵢ (φ₁ φ₂ : π' →ᵢ π'') (ψ : π →ᵢ π') : (φ₁ + φ₂) ∘ᵢ ψ = φ₁ ∘ᵢ ψ + φ₂ ∘ᵢ ψ := by
  ext : 1
  push_cast
  simp

@[simp] lemma sub_compᵢ (φ₁ φ₂ : π' →ᵢ π'') (ψ : π →ᵢ π') : (φ₁ - φ₂) ∘ᵢ ψ = φ₁ ∘ᵢ ψ - φ₂ ∘ᵢ ψ := by
  ext : 1
  push_cast
  simp

@[simp] lemma smul_compᵢ (r : R) (φ : π' →ᵢ π'') (ψ : π →ᵢ π') : (r • φ) ∘ᵢ ψ = r • (φ ∘ᵢ ψ) := by
  ext : 1
  push_cast
  simp

@[simp] lemma zero_comp (φ : π →ᵢ π') : (0 : π' →ᵢ π'') ∘ᵢ φ = 0 := rfl
@[simp] lemma comp_zero (φ : π' →ᵢ π'') : φ ∘ᵢ (0 : π →ᵢ π') = 0 := by
  ext : 1
  apply ContinuousLinearMap.comp_zero

lemma mem_invariants (φ : π →ᵢ π') {m : M} (hm : m ∈ π.invariants) : φ m ∈ π'.invariants := by
  intro
  rw [←comm, hm]

def constᵢ : π →ᵢ I π where
  val := {
    toFun         := ContinuousMap.const G
    map_add' _ _  := by ext; simp
    map_smul' _ _ := by ext; simp
    cont          := ContinuousMap.continuous_const'
  }
  property g m    := by ext; simp [I_apply₄]

def mapᵢ : (π →ᵢ π') →ₗ[R] (I π →ᵢ I π') where
  toFun φ := {
    val := {
      toFun f       := ContinuousMap.comp φ.val f
      map_add' _ _  := by ext; simp
      map_smul' _ _ := by ext; simp
      cont          := ContinuousMap.continuous_postcomp _
    }
    property g f  := by ext; simp [I_apply₄, coe_apply]
  }
  map_add' _ _    := rfl
  map_smul' _ _   := rfl

end omit_instance

omit [TopologicalSpace G] [WeaklyContinuous π] [WeaklyContinuous π'] in
@[simp] lemma comp_id (φ : π →ᵢ π') : φ ∘ᵢ id π = φ := rfl

lemma mapᵢ_compᵢ_constᵢ (φ : π →ᵢ π') : φ.mapᵢ ∘ᵢ constᵢ = constᵢ ∘ᵢ φ := rfl

lemma mapᵢ_compᵢ (φ : π' →ᵢ π'') (ψ : π →ᵢ π') : (φ ∘ᵢ ψ).mapᵢ = φ.mapᵢ ∘ᵢ ψ.mapᵢ := rfl

lemma mapᵢ_compᵢ_mapᵢ (φ : π' →ᵢ π'') (ψ : π →ᵢ π') : φ.mapᵢ ∘ᵢ ψ.mapᵢ = (φ ∘ᵢ ψ).mapᵢ := rfl

end ContinuousIntertwining
end noncategorical

section categorical
open CategoryTheory ContinuousIntertwining WeaklyContinuous
variable (R G)

structure WeaklyContinuousModuleCat extends ModuleCat R where
  [isTopologicalSpace : TopologicalSpace carrier]
  [isIsTopologicalAddGroup : IsTopologicalAddGroup carrier]
  [isContinuousConstSMul : ContinuousConstSMul R carrier]

namespace WeaklyContinuousModuleCat

noncomputable instance : CoeSort (WeaklyContinuousModuleCat R) (Type _) := ⟨fun mod ↦ mod.toModuleCat⟩

instance (mod : WeaklyContinuousModuleCat R) : TopologicalSpace mod := mod.2
instance (mod : WeaklyContinuousModuleCat R) : IsTopologicalAddGroup mod := mod.3
instance (mod : WeaklyContinuousModuleCat R) : ContinuousConstSMul R mod := mod.4

instance : Category (WeaklyContinuousModuleCat R) where
  Hom mod₁ mod₂ := mod₁ →L[R] mod₂
  id _          := ContinuousLinearMap.id R _
  comp φ ψ      := ψ ∘L φ
  id_comp       := by tauto
  comp_id       := by tauto
  assoc         := by tauto

instance : Preadditive (WeaklyContinuousModuleCat R) where
  homGroup mod₁ mod₂    := inferInstanceAs (AddCommGroup (mod₁ →L[R] mod₂))
  add_comp _ _ _ _ _ _  := ContinuousLinearMap.comp_add _ _ _
  comp_add _ _ _ _ _ _  := ContinuousLinearMap.add_comp _ _ _

instance : Linear R (WeaklyContinuousModuleCat R) where
  homModule mod₁ mod₂   := inferInstanceAs (Module R (mod₁ →L[R] mod₂))
  smul_comp _ _ _ _ _ _ := ContinuousLinearMap.comp_smul _ _ _
  comp_smul _ _ _ _ _ _ := ContinuousLinearMap.smul_comp _ _ _

instance (mod₁ mod₂ : WeaklyContinuousModuleCat R) : FunLike (mod₁ ⟶ mod₂) mod₁ mod₂ :=
  inferInstanceAs (FunLike (mod₁ →L[R] mod₂) mod₁ mod₂)

instance : ConcreteCategory (WeaklyContinuousModuleCat R) (fun mod₁ mod₂ ↦ (mod₁ →L[R] mod₂)) where
  hom := id
  ofHom := id

instance (mod : WeaklyContinuousModuleCat R) : TopologicalSpace mod := mod.2
instance (mod : WeaklyContinuousModuleCat R) : IsTopologicalAddGroup mod := mod.3

--lemma sub_apply {rep₁ rep₂ : WeaklyContinuousModuleCat R} (φ₁ φ₂ : rep₁ ⟶ rep₂) (m : rep₁) : (φ₁ - φ₂) m = φ₁ m - φ₂ m := rfl

end WeaklyContinuousModuleCat

structure WeaklyContinuousRep extends WeaklyContinuousModuleCat R where
  rep : Representation R G carrier
  [isWeaklyContinuous : WeaklyContinuous rep]

namespace WeaklyContinuousRep
instance : CoeSort (WeaklyContinuousRep R G) (Type _) := ⟨fun rep ↦ rep.toModuleCat⟩
instance (rep : WeaklyContinuousRep R G) : WeaklyContinuous rep.rep := rep.3

instance : Category (WeaklyContinuousRep R G) where
  Hom rep₁ rep₂ := rep₁.rep →ᵢ rep₂.rep
  id rep := id rep.rep
  comp φ ψ := ψ ∘ᵢ φ
  id_comp := by tauto
  comp_id := by tauto
  assoc   := by tauto

instance : Preadditive (WeaklyContinuousRep R G) where
  homGroup rep₁ rep₂ := inferInstanceAs (AddCommGroup (rep₁.rep →ᵢ rep₂.rep))
  add_comp _ _ _ _ _ _ := compᵢ_add _ _ _
  comp_add _ _ _ _ _ _ := add_compᵢ _ _ _

instance : Linear R (WeaklyContinuousRep R G) where
  homModule rep₁ rep₂ :=  inferInstanceAs (Module R (rep₁.rep →ᵢ rep₂.rep))
  smul_comp _ _ _ _ _ _ := compᵢ_smul _ _ _
  comp_smul _ _ _ _ _ _ := smul_compᵢ _ _ _

instance (rep₁ rep₂ : WeaklyContinuousRep R G) : FunLike (rep₁ ⟶ rep₂) rep₁ rep₂ :=
  inferInstanceAs (FunLike (rep₁.rep →ᵢ rep₂.rep) rep₁ rep₂)

-- omit [TopologicalSpace G] in
-- lemma sub_apply (rep₁ rep₂ : WeaklyContinuousRep R G) (φ₁ φ₂ : rep₁ ⟶ rep₂) (m : rep₁) : (φ₁ - φ₂) m = φ₁ m - φ₂ m := rfl

instance (rep₁ rep₂ : WeaklyContinuousRep R G)  : AddHomClass (rep₁ ⟶ rep₂) rep₁ rep₂ :=
  inferInstanceAs (AddHomClass (rep₁.rep →ᵢ rep₂.rep) rep₁ rep₂)

instance (rep₁ rep₂ : WeaklyContinuousRep R G)  : MulActionHomClass (rep₁ ⟶ rep₂) R rep₁ rep₂ :=
  inferInstanceAs (MulActionHomClass (rep₁.rep →ᵢ rep₂.rep) R rep₁ rep₂)

instance : ConcreteCategory (WeaklyContinuousRep R G) (fun rep₁ rep₂ ↦ (rep₁.rep →ᵢ rep₂.rep)) where
  hom := id
  ofHom := id

variable {R G}

noncomputable def invariants : WeaklyContinuousRep R G ⥤ WeaklyContinuousModuleCat R where
  obj rep := ⟨ModuleCat.of R rep.rep.invariants⟩
  map φ := {
    toFun m := {
      val := φ m.val
      property := mem_invariants φ m.property
    }
    map_add' m₁ m₂ := by ext; apply map_add
    map_smul' r m₁ := by ext; apply map_smul
    cont := Continuous.subtype_map φ.val.cont (fun m hm ↦ mem_invariants φ hm)
  }

instance : (invariants (R := R) (G := G)).Additive := ⟨rfl⟩
instance : (invariants (R := R) (G := G)).Linear R := ⟨fun _ _ ↦ rfl⟩

def ind₁ : WeaklyContinuousRep R G ⥤ WeaklyContinuousRep R G where
  obj rep := ⟨⟨ModuleCat.of R C(G,rep)⟩,I rep.rep⟩
  map φ     := φ.mapᵢ
  map_id    := by tauto
  map_comp  := by tauto

instance : Functor.Additive (ind₁ (R := R) (G := G)) := ⟨by tauto⟩

instance : Functor.PreservesZeroMorphisms (ind₁ (R := R) (G := G)) := ⟨by tauto⟩

def ind₁.const {rep : WeaklyContinuousRep R G} : rep ⟶ ind₁.obj rep := constᵢ

lemma ind₁.map_comp_const {rep₁ rep₂ : WeaklyContinuousRep R G} (φ : rep₁ ⟶ rep₂) :
  const ≫ ind₁.map φ = φ ≫ const := rfl

namespace MultiInd
open WeaklyContinuousRep

def obj (rep : WeaklyContinuousRep R G) : ℕ → (WeaklyContinuousRep R G)
| 0     => ind₁.obj rep
| n + 1 => ind₁.obj (obj rep n)

instance (rep : WeaklyContinuousRep R G) (n : ℕ) : FunLike (obj rep (n + 1)) G (obj rep n) :=
  inferInstanceAs (FunLike C(G,(obj rep n)) G  (obj rep n))

def d (rep : WeaklyContinuousRep R G) : ∀ n : ℕ, obj rep n ⟶ obj rep (n + 1)
| 0     => ind₁.const - ind₁.map ind₁.const
| n + 1 => ind₁.const - ind₁.map (d rep n)

lemma d_zero (rep : WeaklyContinuousRep R G) : d rep 0 = ind₁.const - ind₁.map ind₁.const := rfl
lemma d_succ (rep : WeaklyContinuousRep R G) : d rep (n + 1) = ind₁.const - ind₁.map (d rep n) := rfl

@[simp] lemma start (rep : WeaklyContinuousRep R G) :
    ind₁.const ≫ d rep 0 = 0 := by
  rw [d_zero, Preadditive.comp_sub, sub_eq_zero, ←ind₁.map_comp_const]

@[simp] lemma d_comp_d (rep :  WeaklyContinuousRep R G) (n : ℕ) :
    d rep n ≫ d rep (n + 1) = 0 := by
  induction n with
  | zero =>
    rw [d_succ, Preadditive.comp_sub]
    nth_rw 2 [d_zero]
    rw [Preadditive.sub_comp, ind₁.map_comp_const, sub_sub_cancel, ←Functor.map_comp, start, Functor.map_zero]
  | succ n ih =>
    rw [d_succ (n := n+1), Preadditive.comp_sub]
    nth_rw 2 [d_succ]
    rw [Preadditive.sub_comp, ind₁.map_comp_const, sub_sub_cancel, ←Functor.map_comp, ih, Functor.map_zero]

-- TODO : improve the API to remove the `change` in this proof (see `sub_apply` above).
lemma ExactAt_aux (rep : WeaklyContinuousRep R G) (n : ℕ) (x : G) (f : obj rep (n + 1)) (hf : d rep (n + 1) f = 0) :
    f = d rep n (f x) := by
  rw [d_succ] at hf
  change ind₁.const f - ind₁.map (d rep n) f = 0 at hf
  rw [sub_eq_zero] at hf
  have : (ind₁.const f).toFun x = (ind₁.map (d rep n) f).toFun x := by congr
  exact this

def complex (rep : WeaklyContinuousRep R G) : CochainComplex (WeaklyContinuousRep R G) ℕ where
  X := obj rep
  d i j := dite (j = i + 1) (fun hij ↦ hij ▸ d rep i) (fun _ ↦ 0)
  d_comp_d' _ _ _ h₁ h₂ := by subst h₁ h₂; simp

lemma complex_d_def (rep : WeaklyContinuousRep R G) :
    (complex rep).d i j = dite (j = i + 1) (fun hij ↦ hij ▸ d rep i) (fun _ ↦ 0) := rfl

def map {rep₁ rep₂ : WeaklyContinuousRep R G} (φ : rep₁ ⟶ rep₂) :
    ∀ n : ℕ, obj rep₁ n ⟶ obj rep₂ n
  | 0 => ind₁.map φ
  | n + 1 => ind₁.map (map φ n)

def _root_.WeaklyContinuousRep.MultiInd : WeaklyContinuousRep R G ⥤ CochainComplex (WeaklyContinuousRep R G) ℕ where
  obj := complex
  map φ := {
    f := map φ
    comm' n _ hn := by
      subst hn
      simp only [complex_d_def, dif_pos]
      induction n with
      | zero => simp [map, d_zero, ind₁.map_comp_const, ←Functor.map_comp]
      | succ _ ih => simp [map, d_succ, ind₁.map_comp_const, ←Functor.map_comp, ih]
  }
  map_id rep := by
    ext n : 1
    dsimp only [ComplexShape.up_Rel, dite_eq_ite, ↓dreduceDIte, id_eq, eq_mpr_eq_cast, HomologicalComplex.id_f]
    induction n with
    | zero => rfl
    | succ _ ih => rw [map, ih]; rfl
  map_comp φ ψ := by
    ext n : 1
    dsimp only [ComplexShape.up_Rel, dite_eq_ite, ↓dreduceDIte, id_eq, eq_mpr_eq_cast, HomologicalComplex.comp_f]
    induction n with
    | zero => rfl
    | succ _ ih => rw [map, ih]; rfl

noncomputable def HomogeneousCochains : WeaklyContinuousRep R G ⥤ CochainComplex (WeaklyContinuousModuleCat R) ℕ := by
  exact MultiInd ⋙ invariants (G := G) (R := R).mapHomologicalComplex _

end MultiInd
end WeaklyContinuousRep
end categorical
