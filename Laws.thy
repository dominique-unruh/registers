theory Laws
  imports Axioms "HOL-Library.Rewrite" Misc
begin

notation comp_domain (infixl "\<circ>\<^sub>d" 55)
notation tensor_maps (infixr "\<otimes>" 70)


subsection \<open>Elementary facts\<close>

declare tensor_2hom[simp]
declare id_maps_hom[simp]

lemma maps_2hom_hom_comp2: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. F2 a (G b))\<close>
  apply (rule maps_2hom_sym) apply (rule maps_2hom_hom_comp1) apply (rule maps_2hom_sym) by simp

lemma maps_2hom_right: \<open>maps_2hom F2 \<Longrightarrow> maps_hom (\<lambda>b. F2 a b)\<close>
  apply (rule maps_2hom_left) by (rule maps_2hom_sym)

(* lemma maps_hom_2hom_comp: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. G (F2 a b))\<close>
  unfolding maps_2hom_def 
  using comp_maps_hom[of \<open>\<lambda>a. F2 a _\<close> G]
  using comp_maps_hom[of \<open>\<lambda>b. F2 _ b\<close> G]
  unfolding o_def by auto *)

subsection \<open>Tensor product of homs\<close>

definition "tensor_maps_hom F G = tensor_lift (\<lambda>a b. F a \<otimes> G b)"

lemma maps_2hom_F_tensor_G[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows \<open>maps_2hom (\<lambda>a b. F a \<otimes> G b)\<close>
  apply (rule maps_2hom_hom_comp1, rule maps_2hom_hom_comp2)
  by (rule tensor_2hom assms)+

lemma tensor_maps_hom_hom: "maps_hom F \<Longrightarrow> maps_hom G \<Longrightarrow> maps_hom (tensor_maps_hom F G)"
  unfolding tensor_maps_hom_def apply (rule tensor_lift_hom) by simp

lemma tensor_maps_hom_apply[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows "tensor_maps_hom F G (a \<otimes> b) = F a \<otimes> G b"
  unfolding tensor_maps_hom_def 
  using tensor_existence maps_2hom_F_tensor_G[OF assms] 
  by metis

lemma maps_2hom_F_tensor[simp]: \<open>maps_hom F \<Longrightarrow> maps_2hom (\<lambda>a b. F (a \<otimes> b))\<close>
  using tensor_2hom by (rule maps_hom_2hom_comp)

lemma tensor_extensionality:
  fixes F G :: \<open>('a::domain\<times>'b::domain, 'c::domain) maps_hom\<close>
  assumes [simp]: "maps_hom F" "maps_hom G"
  assumes "(\<And>a b. F (a \<otimes> b) = G (a \<otimes> b))"
  shows "F = G"
proof -
  have \<open>F = tensor_lift (\<lambda>a b. F (a \<otimes> b))\<close>
    by (rule tensor_uniqueness, auto)
  moreover have \<open>G = tensor_lift (\<lambda>a b. G (a \<otimes> b))\<close>
    by (rule tensor_uniqueness, auto)
  moreover note assms(3)
  ultimately show "F = G"
    by simp
qed

lemma left_tensor_hom[simp]: "maps_hom ((\<otimes>) a :: 'b::domain domain_end \<Rightarrow> _)" 
  for a :: "'a::domain domain_end"
  apply (rule maps_2hom_right)
  by (simp add: maps_2hom_right)

lemma right_tensor_hom[simp]: "maps_hom (\<lambda>a::'a::domain domain_end. (\<otimes>) a b)"
  for b :: "'b::domain domain_end"
  by (simp add: maps_2hom_left)

lemma tensor_extensionality3: 
  fixes F G :: \<open>('a::domain\<times>'b::domain\<times>'c::domain, 'd::domain) maps_hom\<close>
  assumes [simp]: \<open>maps_hom F\<close> \<open>maps_hom G\<close>
  assumes "\<And>f g h. F (f \<otimes> g \<otimes> h) = G (f \<otimes> g \<otimes> h)"
  shows "F = G"
proof -
  from assms
  have "(F \<circ> (\<otimes>) a) (b \<otimes> c) = (G \<circ> (\<otimes>) a) (b \<otimes> c)" for a b c
    by auto
  then have "F \<circ> (\<otimes>) a = G \<circ> (\<otimes>) a" for a
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_maps_hom; simp)+
  then have "F (a \<otimes> bc) = G (a \<otimes> bc)" for a bc
    using comp_eq_elim by metis
  then show ?thesis
    by (rule tensor_extensionality[rotated -1]; simp)
qed

lemma tensor_extensionality3':
  fixes F G :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain, 'd::domain) maps_hom\<close>
  assumes [simp]: \<open>maps_hom F\<close> \<open>maps_hom G\<close>
  assumes "\<And>f g h. F ((f \<otimes> g) \<otimes> h) = G ((f \<otimes> g) \<otimes> h)"
  shows "F = G"
proof -
  from assms
  have "(F \<circ> (\<lambda>x. x \<otimes> c)) (a \<otimes> b) = (G \<circ> (\<lambda>x. x \<otimes> c)) (a \<otimes> b)" for a b c
    by auto
  then have "F \<circ> (\<lambda>x. x \<otimes> c) = G \<circ> (\<lambda>x. x \<otimes> c)" for c
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_maps_hom; simp)+
  then have "F (ab \<otimes> c) = G (ab \<otimes> c)" for ab c
    using comp_eq_elim by metis
  then show ?thesis
    by (rule tensor_extensionality[rotated -1]; simp)
qed


subsection \<open>Swap and assoc\<close>

definition \<open>swap = tensor_lift (\<lambda>a b. b \<otimes> a)\<close>

lemma swap_hom[simp]: "maps_hom swap"
  unfolding swap_def apply (rule tensor_lift_hom) 
  apply (rule maps_2hom_sym) by (fact tensor_2hom)

lemma swap_apply[simp]: "swap (a \<otimes> b) = (b \<otimes> a)"
  unfolding swap_def 
  apply (rule tensor_existence[THEN fun_cong, THEN fun_cong])
  apply (rule maps_2hom_sym) by (fact tensor_2hom)

term \<open>(tensor_maps_hom swap id) \<circ> swap \<circ> assoc \<circ> (tensor_maps_hom swap id) \<circ> (swap :: ('a::domain\<times>('b::domain\<times>'c::domain), _) maps_hom)\<close>

definition assoc' :: \<open>('a::domain\<times>('b::domain\<times>'c::domain), ('a\<times>'b)\<times>'c) maps_hom\<close> where 
  "assoc' = (tensor_maps_hom swap id) \<circ> swap \<circ> assoc \<circ> (tensor_maps_hom swap id) \<circ> swap"

lemma assoc'_hom: \<open>maps_hom assoc'\<close>
  by (auto simp: assoc'_def intro!: comp_maps_hom tensor_maps_hom_hom id_maps_hom assoc_hom)

lemma assoc'_apply: \<open>assoc' (tensor_maps a (tensor_maps b c)) =  (tensor_maps (tensor_maps a b) c)\<close>
  unfolding assoc'_def by (simp add: id_maps_hom assoc_apply)

subsection \<open>Pairs and compatibility\<close>

(* TODO: needed? *)
definition compatible0 :: \<open>('a::domain,'c::domain) maps_hom \<Rightarrow> ('b::domain,'c) maps_hom \<Rightarrow> bool\<close> where
  \<open>compatible0 F G \<longleftrightarrow> (\<forall>a b. F a \<circ>\<^sub>d G b = G b \<circ>\<^sub>d F a)\<close>

definition compatible :: \<open>('a::domain,'c::domain) maps_hom \<Rightarrow> ('b::domain,'c) maps_hom \<Rightarrow> bool\<close> where
  \<open>compatible F G \<longleftrightarrow> lvalue F \<and> lvalue G \<and> (\<forall>a b. F a \<circ>\<^sub>d G b = G b \<circ>\<^sub>d F a)\<close>

lemma compatibleI:
  assumes "lvalue F" and "lvalue G"
  assumes \<open>\<And>a b. (F a) \<circ>\<^sub>d (G b) = (G b) \<circ>\<^sub>d (F a)\<close>
  shows "compatible F G"
  using assms unfolding compatible_def by simp

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  by (simp add: compatible_def)

definition pair :: \<open>('a::domain,'c::domain) maps_hom \<Rightarrow> ('b::domain,'c) maps_hom \<Rightarrow> ('a\<times>'b, 'c) maps_hom\<close> where
  \<open>pair F G = tensor_lift (\<lambda>a b. F a \<circ>\<^sub>d G b)\<close>

lemma maps_hom_F_comp_G1:
  assumes \<open>maps_hom G\<close>
  shows \<open>maps_hom (\<lambda>b. F a \<circ>\<^sub>d G b)\<close>
  using assms apply (rule comp_maps_hom[of G \<open>\<lambda>b. F a \<circ>\<^sub>d b\<close>, unfolded comp_def])
  apply (rule maps_2hom_right) using comp_2hom by auto

lemma maps_hom_F_comp_G2:
  assumes \<open>maps_hom F\<close>
  shows \<open>maps_hom (\<lambda>a. F a \<circ>\<^sub>d G b)\<close> 
  using assms apply (rule comp_maps_hom[of F \<open>\<lambda>a. a \<circ>\<^sub>d G b\<close>, unfolded comp_def])
  apply (rule maps_2hom_left) using comp_2hom by auto

lemma maps_2hom_F_comp_G[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows \<open>maps_2hom (\<lambda>a b. F a \<circ>\<^sub>d G b)\<close>
  apply (rule maps_2hom_hom_comp1, rule maps_2hom_hom_comp2)
  by (rule comp_2hom assms)+

lemma pair_hom[simp]:
  assumes "maps_hom F" and "maps_hom G"
  shows "maps_hom (pair F G)"
  unfolding pair_def apply (rule tensor_lift_hom) using assms by simp

lemma pair_apply[simp]:
  assumes \<open>maps_hom F\<close> and \<open>maps_hom G\<close>
  shows \<open>(pair F G) (a \<otimes> b) = (F a) \<circ>\<^sub>d (G b)\<close>
  unfolding pair_def 
  using tensor_existence maps_2hom_F_comp_G[OF assms]
  by metis

lemma pair_lvalue[simp]:
  assumes "compatible F G"
  shows "lvalue (pair F G)"
  apply (rule pair_lvalue_axiom[where F=F and G=G and p=\<open>pair F G\<close>])
  using assms by (auto simp: compatible_def lvalue_hom)
  
lemma compatible3[simp]:
  assumes [simp]: "compatible x y" and "compatible y z" and "compatible x z"
  shows "compatible (pair x y) z"
proof (rule compatibleI)
  have [simp]: \<open>lvalue x\<close> \<open>lvalue y\<close> \<open>lvalue z\<close>
    using assms compatible_def by auto
  then have [simp]: \<open>maps_hom x\<close> \<open>maps_hom y\<close> \<open>maps_hom z\<close>
    using lvalue_hom by blast+
  have "(pair (pair x y) z) ((f \<otimes> g) \<otimes> h) = (pair z (pair x y)) (h \<otimes> (f \<otimes> g))" for f g h
    using assms apply (simp add: compatible_def comp_domain_assoc)
    by (metis comp_domain_assoc)
  then have "(pair (pair x y) z \<circ> swap \<circ> (\<otimes>) h) (f \<otimes> g)
           = (pair z (pair x y) \<circ> (\<otimes>) h) (f \<otimes> g)" for f g h
    by auto
  then have *: "(pair (pair x y) z \<circ> swap \<circ> (\<otimes>) h)
           = (pair z (pair x y) \<circ> (\<otimes>) h)" for h
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_maps_hom pair_hom; simp)+
  have "(pair (pair x y) z) (fg \<otimes> h)
           = (pair z (pair x y)) (h \<otimes> fg)" for fg h
    using *
    using comp_eq_dest_lhs by fastforce
  then show "(pair x y fg) \<circ>\<^sub>d (z h) = (z h) \<circ>\<^sub>d (pair x y fg)" for fg h
    unfolding compatible_def by simp
  show "lvalue z" and  "lvalue (pair x y)"
    by simp_all
qed

lemma compatible3'[simp]:
  assumes "compatible x y" and "compatible y z" and "compatible x z"
  shows "compatible x (pair y z)"
  apply (rule compatible_sym)
  apply (rule compatible3)
  using assms by (auto simp: compatible_sym)

lemma compatible_comp_left[simp]: "compatible x y \<Longrightarrow> lvalue z \<Longrightarrow> compatible (x \<circ> z) y"
  by (simp add: compatible_def lvalue_comp)

lemma compatible_comp_right[simp]: "compatible x y \<Longrightarrow> lvalue z \<Longrightarrow> compatible x (y \<circ> z)"
  by (simp add: compatible_def lvalue_comp)

lemma compatible_comp_inner[simp]: 
  "compatible x y \<Longrightarrow> lvalue z \<Longrightarrow> compatible (z \<circ> x) (z \<circ> y)"
  by (smt (verit, best) comp_apply compatible_def lvalue_comp lvalue_mult)

lemma compatible_lvalue1: \<open>compatible x y \<Longrightarrow> lvalue x\<close>
  by (simp add: compatible_def)
lemma compatible_lvalue2: \<open>compatible x y \<Longrightarrow> lvalue y\<close>
  by (simp add: compatible_def)

lemma pair_comp_tensor:
  assumes "compatible A B" and [simp]: \<open>maps_hom C\<close> and [simp]: \<open>maps_hom D\<close>
  shows "(pair A B) o (tensor_maps_hom C D) = pair (A o C) (B o D)"
proof (rule tensor_extensionality)
  have [simp]: \<open>maps_hom A\<close>
    by (metis assms(1) compatible_lvalue1 lvalue_hom)
  have [simp]: \<open>maps_hom B\<close>
    by (metis (mono_tags, lifting) assms(1) compatible_lvalue2 lvalue_hom)
  show \<open>maps_hom (pair A B \<circ> tensor_maps_hom C D)\<close>
    by (metis assms(1) assms(2) assms(3) comp_maps_hom compatible_lvalue1 compatible_lvalue2 lvalue_hom pair_hom tensor_maps_hom_hom)
  show \<open>maps_hom (pair (A \<circ> C) (B \<circ> D))\<close>
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) comp_maps_hom compatible_lvalue1 compatible_lvalue2 lvalue_hom pair_hom)

  show \<open>(pair A B \<circ> tensor_maps_hom C D) (a \<otimes> b) = pair (A \<circ> C) (B \<circ> D) (a \<otimes> b)\<close> for a b
    by (simp add: comp_maps_hom)
qed

lemma pair_comp_swap[simp]:
  assumes "compatible A B"
  shows "(pair A B) o swap = pair B A"
proof (rule tensor_extensionality)
  have [simp]: "maps_hom A" "maps_hom B"
    apply (metis (no_types, hide_lams) assms compatible_lvalue1 lvalue_hom)
    by (metis (full_types) assms compatible_lvalue2 lvalue_hom)
  then show \<open>maps_hom (pair A B \<circ> swap)\<close>
    by (metis (no_types, hide_lams) comp_maps_hom pair_hom swap_hom)
  show \<open>maps_hom (pair B A)\<close>
    by (metis (no_types, lifting) assms compatible_sym lvalue_hom pair_lvalue)
  show \<open>(pair A B \<circ> swap) (a \<otimes> b) = pair B A (a \<otimes> b)\<close> for a b
    (* Without the "only:", we would not need the "apply subst",
       but that proof fails when instantiated in Classical.thy *)
    apply (simp only: o_def swap_apply)
    apply (subst pair_apply, simp, simp)
    apply (subst pair_apply, simp, simp)
    by (metis (no_types, lifting) assms compatible_def)
qed

lemma pair_comp_assoc[simp]:
  assumes [simp]: \<open>maps_hom F\<close> \<open>maps_hom G\<close> \<open>maps_hom H\<close>
  shows \<open>pair F (pair G H) \<circ> assoc = pair (pair F G) H\<close>
proof (rule tensor_extensionality3')
  show \<open>maps_hom (pair F (pair G H) \<circ> assoc)\<close>
    by (metis assms(1) assms(2) assms(3) assoc_hom comp_maps_hom pair_hom)
  show \<open>maps_hom (pair (pair F G) H)\<close>
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) pair_hom)
  show \<open>(pair F (pair G H) \<circ> assoc) ((f \<otimes> g) \<otimes> h) = pair (pair F G) H ((f \<otimes> g) \<otimes> h)\<close> for f g h
    by (simp add: assoc_apply comp_domain_assoc)
qed

lemma pair_comp_assoc'[simp]:
  assumes [simp]: \<open>maps_hom F\<close> \<open>maps_hom G\<close> \<open>maps_hom H\<close>
  shows \<open>pair (pair F G) H \<circ> assoc' = pair F (pair G H)\<close>
proof (rule tensor_extensionality3)
  show \<open>maps_hom (pair (pair F G) H \<circ> assoc')\<close>
    by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) assoc'_hom comp_maps_hom pair_hom)
  show \<open>maps_hom (pair F (pair G H))\<close>
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) pair_hom)
  show \<open>(pair (pair F G) H \<circ> assoc') (f \<otimes> g \<otimes> h) = pair F (pair G H) (f \<otimes> g \<otimes> h)\<close> for f g h
    by (simp add: assoc'_apply comp_domain_assoc)
qed


subsection \<open>Compatibility simplification\<close>

(* The simproc compatibility_warn produces helpful warnings for "compatible x y"
   subgoals that are probably unsolvable due to missing declarations of 
   variable compatibility facts. *)
simproc_setup "compatibility_warn" ("compatible x y") = \<open>fn m => fn ctxt => fn ct => let
  val (x,y) = case Thm.term_of ct of
                 Const(\<^const_name>\<open>compatible\<close>,_ ) $ x $ y => (x,y)
  val str : string lazy = Lazy.lazy (fn () => Syntax.string_of_term ctxt (Thm.term_of ct))
  fun w msg = warning (msg ^ "\n(Disable these warnings with: using [[simproc del: compatibility_warn]])")
  (* val _ = \<^print> (x,y) *)
  val _ = case (x,y) of (Free(n,T), Free(n',T')) => 
            if String.isPrefix ":" n orelse String.isPrefix ":" n' then 
                      w ("Simplification subgoal " ^ Lazy.force str ^ " contains a bound variable.\n" ^
                      "Try to add some assumptions that makes this goal solvable by the simplifier")
            else if n=n' then (if T=T' then () 
                          else w ("In simplification subgoal " ^ Lazy.force str ^ 
                               ", variables have same name and different types.\n" ^
                               "Probably something is wrong."))
                    else w ("Simplification subgoal " ^ Lazy.force str ^ 
                            " occurred but cannot be solved.\n" ^
                            "Please add assumption/fact  [simp]: \<open>" ^ Lazy.force str ^ 
                            "\<close>  somewhere.")
          | _ => w ("Simplification subgoal " ^ Lazy.force str ^ 
                    "\ncannot be reduced to a compatibility of two variables (such as \<open>compatibility x y\<close>).\n" ^
                    "Try adding a simplification rule that breaks it down (such as, e.g., " ^ @{fact compatible3} ^ ").")
  in NONE end\<close>


(* Abbreviations: "mutually f (x1,x2,x3,\<dots>)" expands to a conjunction
   of all "f xi xj" with i\<noteq>y.

   "each f (x1,x2,x3,\<dots>)" expands to a conjunction of all "f xi". *)

syntax "_mutually" :: "'a \<Rightarrow> args \<Rightarrow> 'b" ("mutually _ '(_')")
syntax "_mutually2" :: "'a \<Rightarrow> 'b \<Rightarrow> args \<Rightarrow> args \<Rightarrow> 'c"

translations "mutually f (x)" => "CONST True"
translations "mutually f (_args x y)" => "f x y \<and> f y x"
translations "mutually f (_args x (_args x' xs))" => "_mutually2 f x (_args x' xs) (_args x' xs)"
translations "_mutually2 f x y zs" => "f x y \<and> f y x \<and> _mutually f zs"
translations "_mutually2 f x (_args y ys) zs" => "f x y \<and> f y x \<and> _mutually2 f x ys zs"

syntax "_each" :: "'a \<Rightarrow> args \<Rightarrow> 'b" ("each _ '(_')")
translations "each f (x)" => "f x"
translations "_each f (_args x xs)" => "f x \<and> _each f xs"

(* Declares the attribute [compat]. If applied to a conjunction 
   of "compatible x y" facts, it will add all of them to the simplifier
   (as [simp] does), but additionally add all "lvalue x", "lvalue y" facts. *)
setup \<open>
let 
fun add (thm:thm) results = 
  Net.insert_term (K true) (Thm.concl_of thm, thm) results
  handle Net.INSERT => results
fun collect thm results = case Thm.concl_of thm of
  Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>conj\<close>,_) $ _ $ _) => 
    collect (@{thm conjunct1} OF [thm]) (collect (@{thm conjunct2} OF [thm]) results)
  | Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>compatible\<close>,_) $ _ $ _) =>
    collect (@{thm compatible_lvalue1} OF [thm]) (collect (@{thm compatible_lvalue2} OF [thm]) (add thm results))
  | _ => add thm results
fun declare thm context = let
  val thms = collect thm (Net.empty) |> Net.entries
  in Simplifier.map_ss (fn ctxt => ctxt addsimps thms) context end
in
Attrib.setup \<^binding>\<open>compatible\<close>
 (Scan.succeed (Thm.declaration_attribute declare))
  "Add 'compatible x y' style rules to simplifier. (Also adds 'lvalue x', 'lvalue y')"
end
\<close>


experiment begin
lemma 
  assumes [compatible]: "mutually compatible (a,b,c)"
  shows True
proof -
  have "lvalue b" by simp
  have "compatible b c" by simp
  have "compatible (pair a b) c" by simp
  show ?thesis by simp
qed
end



subsection \<open>Notation\<close>

bundle lvalue_notation begin
notation tensor_maps_hom (infixr "\<otimes>\<^sub>h" 70)
notation pair ("(_; _)")
notation comp_domain (infixl "\<circ>\<^sub>d" 55)
notation tensor_maps (infixr "\<otimes>" 70)
end

bundle no_lvalue_notation begin
no_notation tensor_maps_hom (infixr "\<otimes>\<^sub>h" 70)
no_notation pair ("(_; _)")
no_notation comp_domain (infixl "\<circ>\<^sub>d" 55)
no_notation tensor_maps (infixr "\<otimes>" 70)
end

end
