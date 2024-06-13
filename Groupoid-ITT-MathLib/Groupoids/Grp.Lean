import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Groupoid.Basic

universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of categories. -/
@[nolint checkUnivs]
def Grp := Bundled Groupoid.{v, u}

namespace Grp
-- Porting note: maybe this coercion should be defined to be `objects.obj`?
instance : CoeSort Grp (Type u) := ⟨Bundled.α⟩

instance str (C : Grp.{v, u}) : Groupoid.{v, u} C := Bundled.str C

/-- Construct a bundled `Grp` from the underlying type and the typeclass. -/
def of (C : Type u) [Groupoid.{v} C] : Grp.{v, u} := Bundled.of C

/-- Bicategory structure on `Grp` -/
instance bicategory : Bicategory.{max v u, max v u} Grp.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  homCategory := fun _ _ => Functor.category
  whiskerLeft {C} {D} {E} F G H η := whiskerLeft F η
  whiskerRight {C} {D} {E} F G η H := whiskerRight η H
  associator {A} {B} {C} D := Functor.associator
  leftUnitor {A} B := Functor.leftUnitor
  rightUnitor {A} B := Functor.rightUnitor
  pentagon := fun {A} {B} {C} {D} {E}=> Functor.pentagon
  triangle {A} {B} {C} := Functor.triangle

/-- `Grp` is a strict bicategory. -/
instance bicategory.strict : Bicategory.Strict Grp.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

/-- Category structure on `Grp` -/
instance category : LargeCategory.{max v u} Grp.{v, u} :=
  StrictBicategory.category Grp.{v, u}

@[simp]
theorem id_map {C : Grp} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
  Functor.id_map f

@[simp]
theorem comp_obj {C D E : Grp} (F : C ⟶ D) (G : D ⟶ E) (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  Functor.comp_obj F G X

@[simp]
theorem comp_map {C D E : Grp} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).map f = G.map (F.map f) := Functor.comp_map F G f

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Grp.{v, u} ⥤ Type u where
  obj C := C
  map F := F.obj

-- Porting note: this instance was needed for CategoryTheory.Category.Cat.Limit
instance (X : Grp.{v, u}) : Groupoid (objects.obj X) := (inferInstance : Groupoid X)

section

attribute [local simp] eqToHom_map

/-- Any isomorphism in `Grp` induces an equivalence of the underlying categories. -/
def equivOfIso {C D : Grp} (γ : C ≅ D) : C ≌ D where
  functor := γ.hom
  inverse := γ.inv
  unitIso := eqToIso <| Eq.symm γ.hom_inv_id
  counitIso := eqToIso γ.inv_hom_id

end
end Grp

end CategoryTheory
