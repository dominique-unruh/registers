theory Tensor_LValues
  imports LValues_Typed Complex_Main
begin


section Matrices

(* TODO: make non-square *)
typedef 'a matrix = "UNIV::('a\<Rightarrow>'a\<Rightarrow>complex) set" by simp
setup_lifting type_definition_matrix

lift_definition tensor :: "'a::finite matrix \<Rightarrow> 'b::finite matrix \<Rightarrow> ('a*'b) matrix" is
  "%A B. \<lambda>(r1,r2) (c1,c2). A r1 c1 * B r2 c2" .

(* TODO associator *)
(* TODO swapper *)

instantiation matrix :: (type) ab_group_add begin
lift_definition plus_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i j. A i j + B i j".
lift_definition minus_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i j. A i j - B i j".
lift_definition uminus_matrix :: "'a matrix \<Rightarrow> 'a matrix" is "%A i j. - A i j".
lift_definition zero_matrix :: "'a matrix" is "\<lambda>i j. 0".
instance sorry
end


instantiation matrix :: (type) "{times,one}" begin
lift_definition times_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i k. (\<Sum>j\<in>UNIV. A i j * B j k)".
lift_definition one_matrix :: "'a matrix" is "\<lambda>i j. if i=j then 1 else 0".
instance apply intro_classes.
end

instantiation matrix :: (finite) ring_1 begin
instance apply intro_classes sorry
end

abbreviation "delta x y == (if x=y then 1 else 0)"

lift_definition matrix_on :: "'b::finite matrix \<Rightarrow> ('a,'b) lvalue \<Rightarrow> 'a matrix" is
  "\<lambda>B x (r::'a) (c::'a). B (fst (split_memory x r)) (fst (split_memory x c))
  * delta (snd (split_memory x r)) (snd (split_memory x c))" .

lemma matrix_on_lift_left:
  assumes compat[simp]: "compatible_lvalues x y"
  defines "xy == lvalue_pair x y"
  shows "matrix_on A x = matrix_on (tensor A 1) xy"
proof (transfer fixing: x y xy, rule ext, rule ext)
  fix A :: "'b \<Rightarrow> 'b \<Rightarrow> complex" and r c

  define xrest yrest xyrest
    where "xrest m = snd (split_memory x m)" 
      and "yrest m = snd (split_memory y m)"
      and "xyrest m = snd (split_memory xy m)" for m

  have [simp]: "valid_lvalue xy"
    unfolding xy_def by simp
  have [simp]: "valid_lvalue x"
    using LValues_Typed.compatible_valid1 compat by blast
  have [simp]: "valid_lvalue y"
    using LValues_Typed.compatible_valid2 compat by blast

  have [simp]: "fst (split_memory x r) = getter x r" for r
    by simp
  have [simp]: "fst (split_memory y r) = getter y r" for r
    by simp

  have [simp]: "fst (split_memory xy r) = (getter x r, getter y r)" for r
    apply (subst fst_split_memory)
    unfolding xy_def by simp_all

  have [simp]: "xrest a = xrest b \<longleftrightarrow> xyrest a = xyrest b \<and> getter y a = getter y b" for a b
    unfolding xrest_def xyrest_def xy_def
    apply (rule split_pair_eq_typed)
    by (rule compat)

  show "A (fst (split_memory x r)) (fst (split_memory x c)) *
           delta (xrest r) (xrest c)
        =
          (\<lambda>(r1, r2) (c1, c2). A r1 c1 * delta r2 c2)
              (fst (split_memory xy r))
              (fst (split_memory xy c))
           *
           delta (xyrest r) (xyrest c)"
    by simp
qed
