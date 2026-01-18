theory Examples
  imports Logic

(*Authour: Duc Than Nguyen *)

begin

consts fn :: "FieldName"

consts default_id :: Identifier
consts other_id :: Identifier
axiomatization where
  ids_distinct [simp]: "other_id \<noteq> default_id"

text {* the method \<lambda>x.x *}
definition
  default_method :: Method
  where
  "default_method \<equiv> Method.make [default_id] (SingleStmt (Return default_id))" 

text {* internal_method(x) {
            this.fn := x;
            return x;
        } 
*}
definition
  internal_method :: Method
  where
  "internal_method \<equiv> Method.make [default_id] (Seq (AssignToField fn default_id) (SingleStmt (Return default_id)))"

consts internal_method_name :: MethodName

definition
  internal_class :: Class
  where
  "internal_class \<equiv> Class.make [fn] ((\<lambda>_. default_method)(internal_method_name := internal_method))"

text {* the external class has a field fn that should hold a reference to internal_obj *}
definition
  external_class :: Class
  where
  "external_class \<equiv> Class.make [] (\<lambda>_. default_method)"

consts 
  internal_class_name :: ClassName
  external_class_name :: ClassName
axiomatization  where
  distinct_classes [simp]: "internal_class_name \<noteq> external_class_name"


definition
  M :: Module
  where
  "M \<equiv> Map.empty(internal_class_name := Some internal_class)"

definition
  M' :: Module
  where
  "M' \<equiv> Map.empty(external_class_name := Some external_class)"

definition 
  internal_obj :: Object
  where
  "internal_obj \<equiv> Object.make internal_class_name (Map.empty(fn := Some (VAddr 0)))"

definition
  external_obj :: Object
  where
  "external_obj \<equiv> Object.make external_class_name (Map.empty)"

consts  internal_addr :: Addr
consts  external_addr :: Addr


definition \<chi> :: Heap 
  where
  "\<chi> \<equiv> Map.empty(internal_addr := Some internal_obj, external_addr := Some external_obj)"

text {* default_id := default_id.internal_method_name(other_id) *}
definition code :: Continuation
  where
  "code \<equiv> Code (SingleStmt (MethodCall default_id default_id internal_method_name [other_id]))"

text {*
  Initial stack says default_id = internal_obj, other_id = 5.
*}
definition \<phi> :: Frame
  where
  "\<phi> \<equiv> Frame.make code (Map.empty(default_id := Some (VAddr internal_addr), other_id := Some (VAddr 5))) external_addr"

definition \<sigma> :: Config
  where
  "\<sigma> \<equiv> ([\<phi>],\<chi>)"

text {* A should say that default_id.fn = other_id *}
definition A :: Assertion where
  "A \<equiv> acompare (=) (EField (EId default_id) fn) (EId other_id)"


term "SomeI" 
lemma
   "Next A M M' \<sigma> = Some True"
  apply(simp add: A_def M_def M'_def \<sigma>_def \<chi>_def Next_def )
  apply (auto split:  option.splits list.splits)  
  apply (rule_tac x = x in  exI)
    apply (rule_tac x = y in  exI)
    apply (simp add: next_visible_def)
    apply (rule conjI)
     apply (simp add: internal_class_def  external_class_def 
            default_method_def  external_obj_def  
            internal_obj_def internal_method_def)
  sorry 
 

end