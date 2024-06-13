import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

/-

-/
section

namespace CategoryTheory.Diagrams

universe v v₂ u u₂


inductive WalkingArrow : Type
  | zero
  | one
  deriving DecidableEq, Inhabited


open WalkingArrow


inductive WalkingArrowHom : WalkingArrow → WalkingArrow → Type
  | morph :  WalkingArrowHom zero one
  | id (X : WalkingArrow) : WalkingArrowHom X X
  deriving DecidableEq


/- Porting note: this simplifies using WalkingArrowHom_id; replacement is below;
simpNF still complains of striking this from the simp list -/
attribute [-simp, nolint simpNF] WalkingArrowHom.id.sizeOf_spec

/-- Satisfying the inhabited linter -/
instance : Inhabited (WalkingArrowHom zero one) where default := WalkingArrowHom.morph


open WalkingArrowHom

/-- Composition of morphisms -/
def WalkingArrowHom.comp :
    -- Porting note: changed X Y Z to implicit to match comp fields in precategory
    ∀ { X Y Z : WalkingArrow } (_ : WalkingArrowHom X Y)
      (_ : WalkingArrowHom Y Z), WalkingArrowHom X Z
  | _, _, _, id _, h => h
  | _, _, _, morph, id one => morph

-- Porting note: adding these since they are simple and aesop couldn't directly prove them
theorem WalkingArrowHom.id_comp
    {X Y : WalkingArrow} (g : WalkingArrowHom X Y) : comp (id X) g = g :=
  rfl

theorem WalkingArrowHom.comp_id
    {X Y : WalkingArrow} (f : WalkingArrowHom X Y) : comp f (id Y) = f := by
  cases f <;> rfl

theorem WalkingArrowHom.assoc {X Y Z W : WalkingArrow}
    (f : WalkingArrowHom X Y) (g: WalkingArrowHom Y Z)
    (h : WalkingArrowHom Z W) : comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

instance WalkingArrowHomCategory : SmallCategory WalkingArrow where
  Hom := WalkingArrowHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

@[simp]
theorem WalkingArrowHom_id (X : WalkingArrow) : WalkingArrowHom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/-- `arrow f` is the diagram in `C` consisting of the  morphism `f` -/
def arrow (f : X ⟶ Y) : WalkingArrow ⥤ C where
  obj x :=
    match x with
    | zero => X
    | one => Y
  map h :=
    match h with
    | WalkingArrowHom.id _ => 𝟙 _
    | morph => f
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;> {dsimp; simp}

@[simp]
theorem arrow_obj_zero (f : X ⟶ Y) : (arrow f).obj zero = X := rfl

@[simp]
theorem arrow_obj_one (f : X ⟶ Y) : (arrow f).obj one = Y := rfl

@[simp]
theorem arrow_map_left (f : X ⟶ Y) : (arrow f).map morph = f := rfl

@[simp]
theorem arrow_functor_obj {F : WalkingArrow ⥤ C} (j : WalkingArrow) :
    (arrow (F.map morph)).obj j = F.obj j := by cases j <;> rfl

/-- Every functor indexing an arrow is naturally isomorphic (actually, equal) to a
    `arrow` -/
@[simps!]
def diagramIsoarrow (F : WalkingArrow ⥤ C) :
    F ≅ arrow (F.map morph) :=
  NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_|_|_) <;> simp)

/-- Construct a morphism between arrows. -/
def arrowHom {X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
    (wf : f ≫ q = p ≫ f') : arrow f ⟶ arrow f' where
  app j :=
    match j with
    | zero => p
    | one => q
  naturality := by
    rintro _ _ ⟨⟩ <;> {dsimp; simp [wf]}

@[simp]
theorem arrowHom_app_zero {X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') :
    (arrowHom f f' p q wf).app zero = p :=
  rfl

@[simp]
theorem arrowHom_app_one {X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') :
    (arrowHom f f' p q wf).app one = q :=
  rfl

/-- Construct a natural isomorphism between functors out of the Walking Arrow from
its components. -/
@[simps!]
def arrow.ext {F G : WalkingArrow ⥤ C} (zero : F.obj zero ≅ G.obj zero)
    (one : F.obj one ≅ G.obj one) (morph : F.map morph ≫ one.hom = zero.hom ≫ G.map morph) : F ≅ G :=
  NatIso.ofComponents
    (by
      rintro ⟨j⟩
      exacts [zero, one])
    (by rintro _ _ ⟨_⟩ <;> simp [morph])

/-- Construct a natural isomorphism between `arrow f` and `arrow f'` given
equalities `f = f'`. -/
@[simps!]
def arrow.eqOfHomEq {f f' : X ⟶ Y} (hf : f = f'):
    arrow f ≅ arrow f' :=
  arrow.ext (Iso.refl _) (Iso.refl _) (by simp [hf])

end Diagrams

/-
section

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]


def arrow_comma_functor : (CategoryTheory.Diagrams.WalkingArrow ⥤ C) ⥤ (Arrow C) where
  obj F := Arrow.mk (F.map CategoryTheory.Diagrams.WalkingArrowHom.morph)
  map η := Arrow.homMk (η.naturality CategoryTheory.Diagrams.WalkingArrowHom.morph).symm
  map_comp := by
    intros F G H η φ
    simp [Arrow.homMk]
    congr

def acomma_arrow_functor : (Arrow C) ⥤ (CategoryTheory.Diagrams.WalkingArrow ⥤ C) where
  obj A := CategoryTheory.Diagrams.arrow A.hom
  map η := by
    apply CategoryTheory.Diagrams.arrowHom

  map_comp := by
    intros F G H η φ
    simp [Arrow.homMk]
    congr
-/
