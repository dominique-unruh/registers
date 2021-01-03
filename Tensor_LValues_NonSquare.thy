theory Tensor_LValues
  imports LValues_Typed Complex_Main
begin


section Matrices

(* TODO: make non-square *)
typedef ('row,'col) matrix = "UNIV::('row\<Rightarrow>'col\<Rightarrow>complex) set" by simp
setup_lifting type_definition_matrix
type_synonym 'a square = "('a,'a) matrix"

lift_definition tensor :: "('ar,'ac) matrix \<Rightarrow> ('br,'bc) matrix \<Rightarrow> ('ar*'br,'ac*'bc) matrix" is
  "%A B. \<lambda>(r1,r2) (c1,c2). A r1 c1 * B r2 c2" .

(* TODO associator *)
(* TODO swapper *)

instantiation matrix :: (type, type) ab_group_add begin
lift_definition plus_matrix :: "('r,'c) matrix \<Rightarrow> ('r,'c) matrix \<Rightarrow> ('r,'c) matrix" is "%A B i j. A i j + B i j".
lift_definition minus_matrix :: "('r,'c) matrix \<Rightarrow> ('r,'c) matrix \<Rightarrow> ('r,'c) matrix" is "%A B i j. A i j - B i j".
lift_definition uminus_matrix :: "('r,'c) matrix \<Rightarrow> ('r,'c) matrix" is "%A i j. - A i j".
lift_definition zero_matrix :: "('r,'c) matrix" is "\<lambda>i j. 0".
instance sorry
end

lift_definition mat_mul :: "('a,'b) matrix \<Rightarrow> ('b,'c) matrix \<Rightarrow> ('a,'c) matrix" is "%A B i k. (\<Sum>j\<in>UNIV. A i j * B j k)".
lift_definition mat_one :: "'a square" is "\<lambda>i j. if i=j then 1 else 0".

abbreviation "delta x y == (if x=y then 1 else 0)"

(*
lift_definition matrix_on :: "('br,'bc) matrix \<Rightarrow> ('a,'br) lvalue \<Rightarrow> ('a,'bc) lvalue \<Rightarrow> 'a square" is
  "\<lambda>B xr xc (r::'a) (c::'a). B (fst (split_memory xr r)) (fst (split_memory xc c))
  * delta (snd (split_memory xr r)) (snd (split_memory xc c))" .

lemma matrix_on_lift_left:
  fixes xc :: "('a,'bc) lvalue" and xr :: "('a,'br) lvalue"
  assumes compatc[simp]: "compatible_lvalues xc y"
  assumes compatr[simp]: "compatible_lvalues xr y"
  defines "xyr == lvalue_pair xr y"
  defines "xyc == lvalue_pair xc y"
  shows "matrix_on A xr xc = matrix_on (tensor A mat_one) xyr xyc"
proof (transfer fixing: xr xc y xyc xyr, rule ext, rule ext)
  fix A :: "'br \<Rightarrow> 'bc \<Rightarrow> complex" and r c

  define xcrest xrrest yrest xycrest xyrrest
    where "xcrest m = snd (split_memory xc m)" 
      and "xrrest m = snd (split_memory xr m)" 
      and "yrest m = snd (split_memory y m)"
      and "xycrest m = snd (split_memory xyc m)"
      and "xyrrest m = snd (split_memory xyr m)" for m

  have [simp]: "valid_lvalue xyc"
    unfolding xyc_def by simp
  have [simp]: "valid_lvalue xyr"
    unfolding xyr_def by simp
  have [simp]: "valid_lvalue xc"
    using LValues_Typed.compatible_valid1 compatc by blast
  have [simp]: "valid_lvalue xr"
    using LValues_Typed.compatible_valid1 compatr by blast
  have [simp]: "valid_lvalue y"
    using LValues_Typed.compatible_valid2 compatc by blast

  have [simp]: "fst (split_memory xc r) = getter xc r" for r
    by simp
  have [simp]: "fst (split_memory xr r) = getter xr r" for r
    by simp
  have [simp]: "fst (split_memory y r) = getter y r" for r
    by simp

  have [simp]: "fst (split_memory xyc r) = (getter xc r, getter y r)" for r
    apply (subst fst_split_memory)
    unfolding xyc_def by simp_all
  have [simp]: "fst (split_memory xyr r) = (getter xr r, getter y r)" for r
    apply (subst fst_split_memory)
    unfolding xyr_def by simp_all

  (* TODO: not true without extra assumptions *)
  have [simp]: "xycrest m = xyrrest m" for m
    sorry

  have [simp]: "xrrest a = xrrest b \<longleftrightarrow> xyrrest a = xyrrest b \<and> getter y a = getter y b" for a b
    unfolding xrrest_def xyrrest_def xyr_def
    apply (rule split_pair_eq_typed)
    by (rule compatr)
  have [simp]: "xcrest a = xcrest b \<longleftrightarrow> xycrest a = xycrest b \<and> getter y a = getter y b" for a b
    unfolding xcrest_def xycrest_def xyc_def
    apply (rule split_pair_eq_typed)
    by (rule compatc)

  show "A (fst (split_memory xr r)) (fst (split_memory xc c)) *
           delta (xrrest r) (xcrest c)
        =
          (\<lambda>(r1, r2) (c1, c2). A r1 c1 * delta r2 c2)
              (fst (split_memory xyr r))
              (fst (split_memory xyc c))
           *
           delta (xyrrest r) (xycrest c)"

    apply simp
    apply auto

    by simp
qed
*)

end