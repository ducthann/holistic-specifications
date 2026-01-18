theory Adaptation
  imports Language

(*Authour: Duc Than Nguyen *)

begin    

(* 
                AssignToField FieldName Identifier (* this.FieldName := Identifier *) |
                ReadFromField Identifier FieldName (* Identifier := this.Fieldname *) |
                MethodCall    Identifier Identifier MethodName "Identifier list" (*Identifier := Identifier.MethodName(Identifier list) *) |
                NewObject     Identifier ClassName "Identifier list" (*Identifier := new ClassName (Identifier list) *) |
                Return        Identifier (*return Identifier *)
 *)

text {* v[y/x] for an identifier v *}
definition ident_subst :: "Identifier \<Rightarrow> Identifier  \<Rightarrow> Identifier \<Rightarrow> Identifier" where
  "ident_subst x y v = (if v = x then y else v)"

text {* s[y/x]: statement s with every occurrence of x replaced by y *}
fun stmt_subst :: "Stmt \<Rightarrow> Identifier \<Rightarrow> Identifier \<Rightarrow> Stmt" where
  "stmt_subst (AssignToField f v) x y = (AssignToField f (ident_subst x y v))" |
  "stmt_subst (ReadFromField v f) x y = (ReadFromField (ident_subst x y v) f)" |
  "stmt_subst (MethodCall v v' m vs) x y = 
     (MethodCall (ident_subst x y v) (ident_subst x y v') m (map (ident_subst x y) vs))" |
  "stmt_subst (NewObject v c vs) x y = (NewObject (ident_subst x y v) c (map (ident_subst x y) vs))" |
  "stmt_subst (Return v) x y = (Return (ident_subst x y v))"

fun stmt_idents :: "Stmt \<Rightarrow> Identifier set" where
  "stmt_idents (AssignToField f v) = {v}" |
  "stmt_idents (ReadFromField v f) = {v}" |
  "stmt_idents (MethodCall v v' m vs) = {v,v'} \<union> (set vs)" |
  "stmt_idents (NewObject v c vs) = {v} \<union> (set vs)" |
  "stmt_idents (Return v) = {v}"

lemma stmt_subst_idents:
  "stmt_idents (stmt_subst s x y) = 
   ((stmt_idents s - {x}) \<union> (if x \<in> stmt_idents s then {y} else {}))"
  by (induction rule: stmt_idents.induct, auto simp: ident_subst_def split: if_splits)

fun stmts_subst :: "Stmts \<Rightarrow> Identifier \<Rightarrow> Identifier \<Rightarrow> Stmts" where
  "stmts_subst (SingleStmt s) x y = (SingleStmt (stmt_subst s x y))" |
  "stmts_subst (Seq s1 s2) x y = (Seq (stmt_subst s1 x y) (stmts_subst s2 x y))"

fun stmts_idents :: "Stmts \<Rightarrow> Identifier set" where
  "stmts_idents (SingleStmt s) = (stmt_idents s)" |
  "stmts_idents (Seq s1 s2) = (stmt_idents s1 \<union> (stmts_idents s2))"

lemma stmts_subst_idents:
  "stmts_idents (stmts_subst s x y) = 
   ((stmts_idents s - {x}) \<union> (if x\<in>stmts_idents s then {y} else {}))"
  by (induction rule: stmts_subst.induct, auto simp: stmt_subst_idents)

term "sorted_list_of_set (X::nat set)"

fun stmts_subst_list :: "Stmts \<Rightarrow> Identifier list \<Rightarrow> Identifier list \<Rightarrow> Stmts" where
  "stmts_subst_list s (v#vs) (v'#vs') = (stmts_subst_list (stmts_subst s v v') vs vs')" |
  "stmts_subst_list s (v#vs) [] = undefined" |
  "stmts_subst_list s [] (v'#vs') = undefined" | 
  "stmts_subst_list s [] [] = s"

(* well-formed for stmts_subst_list *) 
definition stmts_subst_list_wf :: "Stmts \<Rightarrow> Identifier list \<Rightarrow> Identifier list \<Rightarrow> bool" where
"stmts_subst_list_wf s vs vs' \<equiv>  (length vs = length vs') "

lemma stmts_list_idents:
 "stmts_subst_list_wf s vs vs' \<Longrightarrow> (stmts_idents (stmts_subst_list s vs vs')
                                        \<subseteq>  ((stmts_idents s - (set vs)) \<union> (set vs')))"

proof (induction rule: stmts_subst_list.induct)
  case (1 s v vs v' vs')
  from this  
  have assm1:  "stmts_subst_list_wf (stmts_subst s v v') vs vs'" 
              and assm2: "stmts_subst_list_wf (stmts_subst s v v') vs vs' \<Longrightarrow>
                           stmts_idents (stmts_subst_list (stmts_subst s v v') vs vs')
                           \<subseteq> stmts_idents (stmts_subst s v v') - set vs \<union> set vs'" 
    apply  (simp add: stmts_subst_list_wf_def)
  by (simp add: "1.IH")

  from assm1 and assm2 
  have assm3: "stmts_idents (stmts_subst_list (stmts_subst s v v') vs vs')
               \<subseteq> stmts_idents (stmts_subst s v v') - set vs \<union> set vs'"  
    by blast
  from assm3 
  have assm4: "stmts_idents (stmts_subst_list s (v # vs) (v' # vs')) = 
        stmts_idents (stmts_subst_list (stmts_subst s v v') vs vs')" 
    by auto
  from assm1 assm2 assm3 assm4 
  have assm5:  "stmts_idents (stmts_subst s v v') - set vs \<union> set vs'  
                 \<subseteq> (stmts_idents s - set (v # vs) \<union> set (v' # vs'))" 
    using stmts_subst_idents by auto

  from  assm1 assm2 assm3 assm4 assm5
  have assm6: "stmts_idents (stmts_subst_list s (v # vs) (v' # vs')) 
                \<subseteq> (stmts_idents s - set (v # vs) \<union> set (v' # vs'))" 
    by blast
  then show ?case by auto
next
  case (2 s v vs)
  then show ?case by ( auto simp add: stmts_subst_list_wf_def)    
next
  case (3 s v' vs')
  then show ?case by ( auto simp add: stmts_subst_list_wf_def)
next
  case (4 s)
  then show ?case by simp
qed


text {* 
  @{term "fresh_idents X xs"}: 
  Generate a list of fresh identifiers where none of the new identifiers appear in X or in xs 
*}
primrec fresh_idents :: "Identifier set \<Rightarrow> Identifier list \<Rightarrow> Identifier list" where
  "fresh_idents X [] = []" |
  "fresh_idents X (x#xs)  = (let v = fresh_nat (X \<union> (set (x#xs))) in 
                             (v # (fresh_idents (X \<union> {v}) xs)))"

lemma fresh_idents_length [simp]:
  "length (fresh_idents X xs) = length xs"
  apply(induction xs arbitrary: X)
   apply clarsimp+
  by(metis length_Cons)

(*need to have X \<noteq> {} because fresh_nat X = 0 when X = {} *)

lemma fresh_ident_greater:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> fresh_nat X > Max X"
  unfolding Max_def If_def
  by (metis Max_def Max_less_iff fresh_nat_def last_sorted_list_of_list_is_greatest le_imp_less_Suc)

(* TODO: clean up this proof, which currently resorts to sledgehammer-generated Isar *)
lemma fresh_idents_greater:
  "finite X  \<Longrightarrow>  xs \<noteq> [] \<Longrightarrow> (\<forall>x\<in>set (fresh_idents X xs). x > Max (X \<union> set xs))"
  apply(induction xs arbitrary: X)
   apply simp
  apply (clarsimp simp: Let_def)
  apply (rule conjI)
  using fresh_ident_greater apply simp
  apply(rule conjI)
  using fresh_ident_greater apply auto[1]
  apply clarsimp
  apply(subgoal_tac "(insert a (X \<union> set xs)) \<noteq> {} \<and> finite (insert a (X \<union> set xs))")
  using fresh_ident_greater
proof -
  fix a :: nat and xsa :: "nat list" and Xa :: "nat set" and x :: nat
  assume a1: "x \<in> set (fresh_idents (insert (fresh_nat (insert a (Xa \<union> set xsa))) Xa) xsa)"
  assume a2: "\<And>X. \<lbrakk>finite X; xsa \<noteq> []\<rbrakk> \<Longrightarrow> \<forall>x\<in>set (fresh_idents X xsa). \<forall>a\<in>X \<union> set xsa. a < x"
  assume a3: "finite Xa"
  assume a4: "insert a (Xa \<union> set xsa) \<noteq> {} \<and> finite (insert a (Xa \<union> set xsa))"
  have f5: "\<forall>n. n \<notin> set (fresh_idents (insert (fresh_nat (insert a (Xa \<union> set xsa))) Xa) xsa) \<or> (\<forall>na. na \<notin> insert (fresh_nat (insert a (Xa \<union> set xsa))) Xa \<union> set xsa \<or> na < n)"
using a3 a2 by (metis finite.insertI fresh_idents.simps(1) insert_not_empty mk_disjoint_insert set_empty2)
  have f6: "\<forall>n N na. (n::nat) \<notin> N \<and> n \<noteq> na \<or> n \<in> insert na N"
by force
  then have "a < fresh_nat (insert a (Xa \<union> set xsa))"
    using a4 by (metis (no_types) Max_less_iff fresh_ident_greater)
  then have "a < x"
    using f5 a1 by fastforce
  then show "a < x \<and> (\<forall>n\<in>Xa \<union> set xsa. n < x)"
    using f6 f5 a1 by (metis (no_types) Un_insert_left)
next
  fix a xs X x
  show
  "\<lbrakk>\<And>X. \<lbrakk>finite X; xs \<noteq> []\<rbrakk> \<Longrightarrow> \<forall>x\<in>set (fresh_idents X xs). \<forall>a\<in>X \<union> set xs. a < x; finite X;
        x \<in> set (fresh_idents (insert (fresh_nat (insert a (X \<union> set xs))) X) xs);
        \<And>X. \<lbrakk>finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> Max X < fresh_nat X\<rbrakk>
       \<Longrightarrow> insert a (X \<union> set xs) \<noteq> {} \<and> finite (insert a (X \<union> set xs))"
    by blast
qed

lemma fresh_idents_empty: 
"finite X \<Longrightarrow> (set (fresh_idents X xs) \<inter> (X \<union> set xs)) = {}"
proof-
  assume "finite X "
  from this have "(\<forall>x\<in>set (fresh_idents X xs). x > Max (X \<union> set xs))" 
    by (metis empty_iff empty_set fresh_idents.simps(1) fresh_idents_greater)
  then
  show "(set (fresh_idents X xs) \<inter> (X \<union> set xs)) = {}"
    by (meson Int_emptyI List.finite_set Max_ge \<open>finite X\<close> finite_UnI not_le)
qed


lemma fresh_idents_distinct [simp]:
  "finite X \<Longrightarrow> distinct (fresh_idents X xs)"
proof(induction xs arbitrary: X)
  case Nil
  then show ?case by clarsimp
next
  case (Cons a xs)
  show ?case 
  proof (clarsimp simp: Let_def, rule conjI)
    show "fresh_nat (insert a (X \<union> set xs))
    \<notin> set (fresh_idents (insert (fresh_nat (insert a (X \<union> set xs))) X) xs)"
      using fresh_idents_empty 
      using Cons.prems contra_subsetD by blast
  next
    show "distinct (fresh_idents (insert (fresh_nat (insert a (X \<union> set xs))) X) xs)"
      using Cons fresh_idents_empty by simp
  qed
qed

fun 
ident_subst_list :: "Identifier \<Rightarrow> Identifier list \<Rightarrow> Identifier list \<Rightarrow> Identifier"
  where
  "ident_subst_list x (v#vs) (v'#vs') = (ident_subst v v' x)" |
  "ident_subst_list x (v#vs) [] = undefined" |
  "ident_subst_list x [] (v'#vs') = undefined" | 
  "ident_subst_list x [] [] = x"

value "ident_subst_list x [1] []" 

fun 
cont_subst_list :: "Continuation \<Rightarrow> Identifier list \<Rightarrow> Identifier list \<Rightarrow> Continuation" 
  where
   "cont_subst_list (Code stmts) vs vs' = (Code (stmts_subst_list stmts vs vs'))" |
   "cont_subst_list (NestedCall x stmts) vs vs' = 
      (NestedCall (ident_subst_list x vs vs') (stmts_subst_list stmts vs vs'))"

text{*Definition of Adaptation *}

definition adapt_frame :: "Frame \<Rightarrow> Frame \<Rightarrow> Frame"
  where
  "adapt_frame \<phi> \<phi>' \<equiv> 
     (let zs = sorted_list_of_set (dom (vars \<phi>'));
          zs' = fresh_idents (dom (vars \<phi>)) zs;
          contn'' = cont_subst_list (cont \<phi>') zs zs' ;
          vars'' = map_upds (vars \<phi>) zs' (map (\<lambda>z. the ((vars \<phi>') z)) zs) in \<lparr>cont = contn'', vars = vars'', this = (this \<phi>')\<rparr>)"

term "map_upds (vars \<phi>) zs' (map (\<lambda>z. the ((vars \<phi>') z)) zs)"
term "(cont_subst_list (cont \<phi>') zs zs')"

definition adaptation :: " Config \<Rightarrow> Config \<Rightarrow> Config option" (" _\<lhd> _") 
  where 
"\<sigma> \<lhd> \<sigma>' \<equiv> (case \<sigma> of (\<phi>#_,_) \<Rightarrow>
             (case \<sigma>' of (\<phi>'#\<psi>',\<chi>') \<Rightarrow> 
               let \<phi>'' = adapt_frame \<phi> \<phi>' in Some (\<phi>''#\<psi>',\<chi>') | _ \<Rightarrow> None) | _ \<Rightarrow> None)" 

fun StmtsContn:: "Continuation \<Rightarrow> Stmts"
  where
"StmtsContn contn = (case contn of (Code stmts) \<Rightarrow> stmts | (NestedCall z stmts) \<Rightarrow> stmts)"


(* lemmas for adaptation to config and config' *) 
lemma adapt_to_config:
"finite (dom (vars \<phi>)) \<Longrightarrow> \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow> 
  w \<in> dom (vars \<phi>'') \<Longrightarrow> w \<in> dom (vars \<phi>) \<Longrightarrow> 
  (vars \<phi>'' w) = (vars \<phi> w)"

  unfolding adapt_frame_def Let_def  
  using  Frame.select_convs(2) UnCI disjoint_iff_not_equal fresh_idents_empty map_upds_apply_nontin
  by metis


lemma adapt_to_config': 
"finite (dom (vars \<phi>)) \<Longrightarrow>  \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow>   
  w \<notin> dom (vars \<phi>)\<Longrightarrow>   w \<in> dom (vars \<phi>'')  \<Longrightarrow>  
  \<exists>v. (v \<in> dom (vars \<phi>') \<longrightarrow>  (vars \<phi>'' w = vars \<phi>' v) \<and> w \<notin> dom (vars \<phi>'))"

  unfolding adapt_frame_def Let_def
  using Frame.select_convs(2) fresh_nat_is_fresh list.simps(8) map_upds_Nil2 sorted_list_of_set.infinite
  by metis


lemma adapt_to_config_config': 
"finite (dom (vars \<phi>)) \<Longrightarrow>  \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow> 
  w \<in> dom (vars \<phi>'') \<Longrightarrow> 
  (w \<notin> dom (vars \<phi>) \<and>  (\<exists>v. v \<in> dom (vars \<phi>') \<longrightarrow>  vars \<phi>'' w =  vars \<phi>' v \<and> w \<notin> dom (vars \<phi>')) \<or> 
  (w \<in> dom (vars \<phi>) \<and>  (vars \<phi>'' w = vars \<phi> w)))"

  using adapt_to_config'  adapt_to_config
  by meson

(*
if v \<in> dom (vars \<phi>') \<and> v \<in> dom (vars \<phi>)
then \<exists> w. w \<in> dom (vars \<phi>''), and 
((vars \<phi>'' w =  vars \<phi>' v) \<or> (vars \<phi>'' w = vars \<phi> v ))
*)

lemma w_dom_config''_config_or_config': 
" finite (dom (vars \<phi>)) \<Longrightarrow>  \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow> 
  v \<in> dom (vars \<phi>')  \<Longrightarrow> v \<in> dom (vars \<phi>)\<Longrightarrow>  
  \<exists> w. w \<in> dom (vars \<phi>'') \<and> ((vars \<phi>'' w =  vars \<phi>' v) \<or> (vars \<phi>'' w = vars \<phi> v ))"

  unfolding adapt_frame_def Let_def
  by (metis Frame.select_convs(2) IntI UnCI dom_map_upds empty_iff fresh_idents_empty map_upds_apply_nontin)

(*
lemma 
"M, \<sigma> \<leadsto> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> 
\<phi>'' = adapt_frame \<phi> \<phi>'
 \<Longrightarrow> z \<in> dom (vars \<phi>'') \<Longrightarrow> finite (dom (vars \<phi>))
\<Longrightarrow> z \<in> stmts_idents (StmtsCode \<phi>'') 
\<Longrightarrow> (\<exists>v. v \<in> stmts_idents (StmtsCode \<phi>) \<and>  vars \<phi>'' z = vars \<phi> v)"
  sorry
*)



end