import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

/-

-/
section

namespace CategoryTheory.Diagrams

universe v v₂ u u₂


inductive WalkingTriangle : Type
  | zero
  | one
  | two
  deriving DecidableEq, Inhabited


open WalkingTriangle

inductive WalkingTriangleHom : WalkingTriangle → WalkingTriangle → Type
  | left :  WalkingTriangleHom zero one
  | right : WalkingTriangleHom one two
  | middle : WalkingTriangleHom zero two
  | id (X : WalkingTriangle) : WalkingTriangleHom X X
  deriving DecidableEq


/- Porting note: this simplifies using WalkingTriangleHom_id; replacement is below;
simpNF still complains of striking this from the simp list -/
attribute [-simp, nolint simpNF] WalkingTriangleHom.id.sizeOf_spec

open WalkingTriangleHom

/-- Composition of morphisms -/
def WalkingTriangleHom.comp :
    -- Porting note: changed X Y Z to implicit to match comp fields in precategory
    ∀ { X Y Z : WalkingTriangle } (_ : WalkingTriangleHom X Y)
      (_ : WalkingTriangleHom Y Z), WalkingTriangleHom X Z
  | _, _, _, id _, h => h
  | _, _, _, h, id _ => h
  |_, _, _, left, right => middle

-- Porting note: adding these since they are simple and aesop couldn't directly prove them
theorem WalkingTriangleHom.id_comp
    {X Y : WalkingTriangle} (g : WalkingTriangleHom X Y) : comp (id X) g = g := by
    cases g <;> rfl

theorem WalkingTriangleHom.comp_id
    {X Y : WalkingTriangle} (f : WalkingTriangleHom X Y) : comp f (id Y) = f := by
  cases f <;> rfl

theorem WalkingTriangleHom.assoc {X Y Z W : WalkingTriangle}
    (f : WalkingTriangleHom X Y) (g: WalkingTriangleHom Y Z)
    (h : WalkingTriangleHom Z W) : comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

instance WalkingTriangleHomCategory : SmallCategory WalkingTriangle where
  Hom := WalkingTriangleHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

@[simp]
theorem WalkingTriangleHom_id (X : WalkingTriangle) : WalkingTriangleHom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

/-- `triangle f g` is the diagram in `C`-/
def triangle (f : X ⟶ Y)(g : Y ⟶ Z) : WalkingTriangle ⥤ C where
  obj x :=
    match x with
    | zero => X
    | one => Y
    | two => Z
  map h :=
    match h with
    | WalkingTriangleHom.id _ => 𝟙 _
    | left => f
    | right => g
    | middle => f ≫ g
  map_comp := by
    rintro _ _ _ ⟨⟩ h <;> cases h <;> {dsimp ; simp [CategoryStruct.comp,WalkingTriangleHom.comp]}

@[simp]
theorem triangle_obj_zero (f : X ⟶ Y)(g : Y ⟶ Z) : (triangle f g).obj zero = X := rfl

@[simp]
theorem triangle_obj_one (f : X ⟶ Y)(g : Y ⟶ Z) : (triangle f g).obj one = Y := rfl

@[simp]
theorem triangle_obj_two (f : X ⟶ Y)(g : Y ⟶ Z) : (triangle f g).obj two = Z := rfl

@[simp]
theorem triangle_map_left (f : X ⟶ Y)(g : Y ⟶ Z) : (triangle f g).map left = f := rfl

@[simp]
theorem triangle_map_right (f : X ⟶ Y)(g : Y ⟶ Z) : (triangle f g).map right = g := rfl

@[simp]
theorem triangle_map_middle (f : X ⟶ Y)(g : Y ⟶ Z) : (triangle f g).map middle = f ≫ g := rfl

@[simp]
theorem map_middle (F : WalkingTriangle ⥤ C) : F.map middle = F.map left ≫ F.map right := by
  rw [<- F.map_comp]
  simp [CategoryStruct.comp, WalkingTriangleHom.comp]


@[simp]
theorem triangle_functor_obj {F : WalkingTriangle ⥤ C} (j : WalkingTriangle) :
    (triangle (F.map left) (F.map right)).obj j = F.obj j := by cases j <;> rfl

/-- Every functor indexing an triangle is naturally isomorphic (actually, equal) to a
    `triangle` -/
@[simps!]
def diagramIsotriangle (F : WalkingTriangle ⥤ C) :
    F ≅ triangle (F.map left) (F.map right) :=
  NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_|_|_) <;>simp)

/-- Construct a morphism between triangles. -/
def triangleHom {X' Y' Z': C} (f : X ⟶ Y)(f' : X' ⟶ Y')(g : Y ⟶ Z) (g' : Y' ⟶ Z') (p : X ⟶ X') (q : Y ⟶ Y')(r : Z ⟶ Z')
    (wf : f ≫ q = p ≫ f') (wg : g ≫ r = q ≫ g') : triangle f g ⟶ triangle f' g' where
  app j :=
    match j with
    | zero => p
    | one => q
    | two => r
  naturality := by
    rintro _ _ ⟨⟩ <;> simp [wg,wf]
    rw [<- Category.assoc, wf,<- Category.assoc]

@[simp]
theorem triangleHom_app_zero {X' Y' Z': C} (f : X ⟶ Y)(f' : X' ⟶ Y')(g : Y ⟶ Z) (g' : Y' ⟶ Z') (p : X ⟶ X') (q : Y ⟶ Y')(r : Z ⟶ Z')
    (wf : f ≫ q = p ≫ f') (wg : g ≫ r = q ≫ g'):
    (triangleHom f f' g g' p q r wf wg).app zero = p :=
  rfl

@[simp]
theorem triangleHom_app_one {X' Y' Z': C} (f : X ⟶ Y)(f' : X' ⟶ Y')(g : Y ⟶ Z) (g' : Y' ⟶ Z') (p : X ⟶ X') (q : Y ⟶ Y')(r : Z ⟶ Z')
    (wf : f ≫ q = p ≫ f') (wg : g ≫ r = q ≫ g'):
    (triangleHom f f' g g' p q r wf wg).app one = q :=
  rfl

@[simp]
theorem triangleHom_app_two {X' Y' Z': C} (f : X ⟶ Y)(f' : X' ⟶ Y')(g : Y ⟶ Z) (g' : Y' ⟶ Z') (p : X ⟶ X') (q : Y ⟶ Y')(r : Z ⟶ Z')
    (wf : f ≫ q = p ≫ f') (wg : g ≫ r = q ≫ g'):
    (triangleHom f f' g g' p q r wf wg).app two = r :=
  rfl

/-- Construct a natural isomorphism between functors out of the Walking triangle from
its components. -/
@[simps!]
def triangle.ext {F G : WalkingTriangle ⥤ C} (zero : F.obj zero ≅ G.obj zero)
    (one : F.obj one ≅ G.obj one) (two : F.obj two ≅ G.obj two) (left : F.map left ≫ one.hom = zero.hom ≫ G.map left)
    (right : F.map right ≫ two.hom = one.hom ≫ G.map right) : F ≅ G :=
  NatIso.ofComponents
    (by
      rintro ⟨j⟩
      exacts [zero, one, two])
    (by rintro _ _ ⟨_⟩ <;> simp [right] ; case middle ; rw [<- Category.assoc] ; all_goals {simp [left]})

/-- Construct a natural isomorphism between `triangle f` and `triangle f'` given
equalities `f = f'`. -/
@[simps!]
def triangle.eqOfHomEq {f f' : X ⟶ Y} {g g' : Y ⟶ Z} (hf : f = f') (hg : g = g'):
    triangle f g ≅ triangle f' g' :=
  triangle.ext (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hf]) (by simp [hg])

end Diagrams
