functor ImproveTwo (S: IMPROVE_TWO_STRUCTS): IMPROVE_TWO =
struct

open S
open Exp Transfer
structure IL = IntervalLattice(S)
open List

structure VarInfo =
  struct


    datatype t = T of {var: Var.t,
		       il: IL.t ref,
		       cMax: int ref,
		       cMin: int ref}

    fun new (x: Var.t, w: WordSize.t option) = T {var = x,
						  il = ref (IL.new(w)),
						  cMax = ref 0,
						  cMin = ref 0}
    fun layout (T {var,il,cMin,cMax}) = 
	let open Layout
	in record [("ILVar", Var.layout var),
		   ("ILIL", IL.layout (!il)),
		   ("ILMIN", Layout.str (Int.toString (!cMin))),
		   ("ILMAX", Layout.str (Int.toString (!cMax)))]
	end
    fun setConst (T {il,...}, c: IntInf.t)= 
	IL.setConstant (!il, c)

    fun sameVar (T {var=var1,...}, T {var=var2,...}) = 
	Var.equals (var1,var2)
 
    fun findC (oper, cs, t, start) =
	let
	    fun visit ([], l) = l
	      | visit ((c::cs'), l) = if oper (c,t)
				      then l
				      else visit (cs',IL.V c)
	in
	    visit (cs, start)
	end

    fun joinValues (T {il,cMin,cMax,...}, il2, cs) = 
	case IL.value (!il) of
	    IL.Interval (e1,e2) =>
	    let
		val () = IL.<= (!il,il2)
	    in 
		case IL.value (!il) of
		    IL.Interval (e1New,e2New) =>
		    let
			val () = case e1New of
				     IL.V ex => if IL.elmLt (e1New,e1)
					     then 
						 if (!cMin) = 0
						 then cMin := 1
						 else (IL.setLowerElm (!il, findC ((op <),cs,ex,IL.MIN))
						     ;
						     cMin := 0)
					     else ()
				   | _ => ()
					  
			val () = case e2New of
				     IL.V ex => if IL.elmLt (e2,e2New)
					     then 
						 if (!cMax) = 0
						 then cMax := 1
						 else (IL.setHigherElm (!il, findC ((op >),(List.rev cs), ex, IL.MAX));
						     cMax := 0)
					     else ()
				   | _ => ()
(*			val () = if (!cMin) > 7
				 then IL.makeMin (!il)
				 else ()
			val () = if (!cMax) > 7
				 then IL.makeMax (!il)
				 else ()*)
		    in 
			()
		    end
		  | _ => ()
	    end
	  | _ => IL.<= (!il,il2)

    fun makeTop (T {il,...}) = 
	IL.makeTop (!il)

    
    fun setValue (T {il,...}, v) =
	il := v
    fun il (T {il,...}) = !il
    fun var (T {var,...}) = var
    fun clone (T {il=il',var,...}, cs) = 
	let
	    val newvi = new(var,(IL.size (!il')))
	    val () = joinValues(newvi, (!il'), cs)
	in
	    newvi
	end
  end

structure BoolInfo =
  struct


    datatype t = T of {var: Var.t option ref,
		       tr: IL.t option ref,
		       fa: IL.t option ref,
		       size: WordSize.t option}
		      
    fun new (x: Var.t, t: IL.t option, f: IL.t option, size: WordSize.t option) = T {var = ref (SOME x),
										     tr = ref t,
										     fa = ref f,
										     size = size}

    fun newEmpty () = T {var = ref NONE,
			 tr = ref NONE,
			 fa = ref NONE,
			 size = NONE}
						     
    fun layout (T {var,tr,fa,...}) =
	let open Layout
	in
	    record [("BINF_VAR", Option.layout Var.layout (!var)),
		    ("BINF_T", Option.layout IL.layout (!tr)),
		    ("BINF_F", Option.layout IL.layout (!fa))]
	end
	
    fun isSomething (T {tr,fa,...}) = case (!tr,!fa) of 
					  (NONE,NONE) => false
					| (_,_) => true

    fun tr (T {tr,...}) = tr
    fun fa (T {fa,...}) = fa
    fun var (T {var,...}) = var
    fun size (T {size,...}) = size
  end

structure LabelInfo =
  struct
  
    datatype t = T of {args: (Var.t * Type.t) vector,
		       ancestor: Label.t option ref,
		       facts: VarInfo.t list ref}
		    
    fun new (args) = T {args = args,
			ancestor = ref NONE,
			facts = ref []}
		     
    fun layout (T {args,ancestor,facts}) = 
	let open Layout
	in 
	    record [("LINF_A", Option.layout Label.layout (!ancestor)),
		    ("LINF_F", List.layout VarInfo.layout (!facts))]
	end

    fun ancestor (T {ancestor,...}) = ancestor
    fun facts (T {facts,...}) = facts
    fun args (T {args,...}) = args
  end

structure FuncInfo = 
  struct

		   
    datatype t = T of {args: (Var.t * Type.t) vector}

    fun new args = T {args = args}
    fun layout (T {args}) = 
	let open Layout
	in 
	    Vector.layout (Layout.tuple2 (Var.layout,Type.layout)) args
	end

    fun args (T {args}) = args
  end



fun improve (Program.T {datatypes, globals, functions, main}) =
    let 
	val {get = varInfo: Var.t -> VarInfo.t,
	     set = setVarInfo, ...} = 
	    Property.getSet (Var.plist,
			     Property.initFun (fn x=>VarInfo.new (x,NONE)))
	
	val {get = boolInfo: Var.t -> BoolInfo.t*BoolInfo.t,
	     set = setBoolInfo, ...} = 
	    Property.getSet (Var.plist,
			     Property.initFun (fn x=>(BoolInfo.newEmpty (), BoolInfo.newEmpty ())))

	val {get = labelInfo: Label.t -> LabelInfo.t,
	     set = setLabelInfo, ...} =
            Property.getSetOnce
                     (Label.plist, 
		      Property.initRaise ("ImproveTwo.labelInfo", Label.layout))
		     (*Property.initFun (fn _ => LabelInfo.new (ref NONE, ref [])))*)

	val {get = funcInfo: Func.t -> FuncInfo.t,
             set = setFuncInfo, ...} =
            Property.getSetOnce
		(Func.plist,
		 Property.initRaise ("ImproveTwo.funcInfo", Func.layout))
	    
	fun insertSort R [] = []
	  | insertSort R (h::t) =
            let fun insert R [] x = [x]
		  | insert R (h::t) x = if R (x, h) then x::(h::t)
					else h::(insert R t x)
		val rest = insertSort R t
	    in  insert R rest h
	    end;
	    
	val i = insertSort;


	(* deleting all occurences of an element from a list *)
	fun delete A nil = nil 
	  | delete A (B::R) = if (A=B) then (delete A R) else (B::(delete A R));
	    
	(* remove duplicates from a list *)
	fun remDups nil = nil     	
	  | remDups (A::R) = (A::(remDups (delete A R)));
	   

	val constants = remDups (i (op <) (Vector.toList (Vector.keepAllMap (globals, fn (Statement.T {exp,ty,...}) =>
	   case Type.dest ty of
	       Type.Word _ => (case exp of
			      Const (Const.Word wx) => SOME (WordX.toIntInf wx)
			      | _ => NONE)
	     | _ => NONE))))
 

	(* Statement.T -> unit*)
	fun visitGlobalStatement (Statement.T {var,exp,ty}) =
	    case Type.dest ty of
		Type.Word w => (case exp of
				   Const (Const.Word wx) => Option.app (var, fn x=> (setVarInfo (x, VarInfo.new (x,SOME w)); VarInfo.setConst (varInfo x, WordX.toIntInf wx)))
				 | _ => ())
	      | _ => ()

	fun sizeFromType t =
	    case Type.dest t of
		Type.Word size => SOME size
	      | _ => NONE

	fun findVarInfo (vs, v) = 
	    let
		fun visit (v'::vs') = 
		    let
			val var = VarInfo.var v'
		    in 
			if Var.equals (v,var) 
			then SOME v'
			else visit vs'
		    end
		  | visit [] = NONE
	    in
		visit vs
	    end

	fun findFact (l, v) =
	    case l of
		NONE => varInfo v
	      | SOME lab =>
		    let 
			val li = labelInfo lab
			val facts = !(LabelInfo.facts li)
			val ancestor = !(LabelInfo.ancestor li)
		    in
			case findVarInfo(facts,v) of
			    SOME vi => vi
			  | NONE => findFact (ancestor,v)
		    end

		

	fun removeFromBound (il,v) =
	    let
		val value = WordX.toIntInf v		
	    in
		case IL.value il of
		    IL.Interval (e1,e2) =>
		    let
			val low = case e1 of
				      IL.V v1 => if v1=value
						 then SOME (IL.addOneLow il)
						 else NONE
				    | _ => NONE
			val high = case e2 of
				       IL.V v2 => if v2=value
						  then SOME (IL.subOneHigh il)
						  else NONE
				     | _ => NONE
		    in
			case low of
			    SOME t => SOME t
			  | _ => high
		    end
		  | _ => NONE
		    
	    end
	    
	fun labelArgsTop l =
	    let
		val args = LabelInfo.args (labelInfo l)
	    in
		Vector.foreach (args, fn (v,t) => 
					 (case Type.dest t of
					      Type.Word _ => VarInfo.makeTop (varInfo v)
					    | _ => ()))
	    end

	fun visitTransfer (t,l,visitArith) =
	    case t of
		Call {args,func,return} =>
		let
		    val formals = FuncInfo.args (funcInfo func)
		    val () = case return of
				 Return.NonTail {cont,...} => labelArgsTop cont

			       | _ => ()
		in
		    Vector.foreach2(formals, args, fn ((v,_),a) => VarInfo.joinValues (varInfo v, VarInfo.il (findFact (SOME l,a)),constants))
		end
	      | Goto {dst,args} =>
		let
		    val formals = LabelInfo.args (labelInfo dst)
		in 
		    Vector.foreach2(formals,args, fn ((v,_),a) => VarInfo.joinValues (varInfo v, VarInfo.il (findFact (SOME l,a)),constants))
		end
	      | Arith {prim,args,success,...} =>
		if (Vector.length args) >= 2 andalso visitArith then 
		    let 
			exception SUCC1
			val succArgs = LabelInfo.args (labelInfo success)
			val () = if Vector.length succArgs < 1 then raise SUCC1 else () 
			val (formal,formalTy) = Vector.sub(succArgs,0)
			val arg0 = VarInfo.il (findFact (SOME l,Vector.sub(args,0)))
			val arg1 = VarInfo.il (findFact (SOME l,Vector.sub(args,1)))
			fun flowToSuccess (il,size) =
			    VarInfo.joinValues (varInfo formal, il, constants)
			fun makeSub (size,signed) = 
			    flowToSuccess (IL.sub_check (arg0,arg1,size,signed),size)
			fun makeAdd (size,signed) =
			    flowToSuccess (IL.add_check (arg0,arg1,size,signed),size)
			fun makeMul (size,signed) = 
			    flowToSuccess (IL.mul_check (arg0,arg1,size,signed),size)
			datatype z = datatype Prim.Name.t
		    in
			case Prim.name prim of
			    Word_subCheck (size,{signed=signed}) => makeSub (size,signed)
			  | Word_addCheck (size,{signed=signed}) => makeAdd (size,signed)
			  | Word_mulCheck (size,{signed=signed}) => makeMul (size,signed)
			  | _ => case sizeFromType formalTy of
				     SOME s => (setVarInfo (formal, VarInfo.new (formal, SOME s)); VarInfo.makeTop (varInfo formal))
				   | _ => ()
			    (*x => Control.diagnostics (fn display => display (Layout.seq [Layout.str "PRIMDEBUG:",
										  Prim.layout prim]))*)
		    end
		else ()
	      | Case {test, cases, default, ...} =>
		((case cases of
		     Cases.Word (size,ws) => Vector.foreach(ws, fn (_,lab) => labelArgsTop lab)
		   | Cases.Con cs  => Vector.foreach (cs, fn (_,lab) => labelArgsTop lab));
		 (case default of
		      SOME lab=>labelArgsTop lab
		    | _ => ()
		 ))
		
	      | _ => ()

	(* Var.t * Type.t -> unit *)
	fun newVarInfo (var, ty) =
	    case Type.dest ty of
		Type.Word w => setVarInfo (var, VarInfo.new(var,SOME w))
	      | _ => ()

	(*Collect the constants from globals*)
	val () = Vector.foreach (globals, visitGlobalStatement)

	(*Initialize all Word variables used as parameters with a VarInfo*)
	val () = 
	    List.foreach
	    (functions, fn function =>
             let 
		 val {args,blocks,name,...} = Function.dest function
		 val fi = FuncInfo.new (args)
		 val () = setFuncInfo (name,fi)
		 val () = Vector.foreach (args, newVarInfo)
		 val () = Vector.foreach (blocks, fn block as Block.T {args=argslabel,label,...} =>
					  let
					      val li = LabelInfo.new (argslabel)
					      val () = setLabelInfo (label, li)
					      val () = Vector.foreach (args,newVarInfo)
					  in ()
					  end)
	     in 
		 ()
	     end)

	(* Visit all blocks *)
	fun propagate visitArith =
	    List.foreach
	    (functions, fn function =>
	     let
		 val {blocks,...} = Function.dest function
		 val () = Vector.foreach (blocks, fn Block.T {statements,transfer,label,...} =>
						     let
							 val () = visitTransfer (transfer,label,visitArith)
						     in ()
						     end)
	     in ()
	     end)
	
	val () = (propagate false; propagate false)

	fun makeBoolInfo {args,prim,...} = 
	    let 
		fun arg i = 
		    let
			val x = Vector.sub (args,i)
		    in
			VarInfo.il (varInfo x)
		    end
		fun makeLt (size,signed)=
		    let
			val a0IL = arg 0
			val a1IL = arg 1
			val (new0t, new0f) = IL.newBoundLT (a0IL,a1IL,size,signed)
			val (new1t, new1f) = IL.newBoundGTEQ(a1IL,a0IL,size,signed)
			val new0tO = if IL.equals (a0IL,new0t) 
				     then NONE
				     else SOME new0t
			val new0fO = if IL.equals (a0IL,new0f)
				     then NONE
				     else SOME new0f
			val new1tO = if IL.equals (a1IL,new1t)
				     then NONE
				     else SOME new1t
			val new1fO = if IL.equals (a1IL,new1f)
				     then NONE
				     else SOME new1f
		    in
			SOME ((BoolInfo.new (Vector.sub(args,0), new0tO,new0fO,SOME size), 
			       BoolInfo.new (Vector.sub(args,1), new1tO,new1fO,SOME size)))
		    end
		datatype z = datatype Prim.Name.t
	    in
		case Prim.name prim of
		    Word_lt (size,signed) => makeLt(size,signed)
		    
		  | _ => NONE
	    end

	fun joinBoolInfo (x, (bi0,bi1)) =
	    let 
		exception WRONG_VAR
		val (biX0,biX1) = boolInfo x
		val var0 = case !(BoolInfo.var bi0) of
			       NONE => raise WRONG_VAR
			     | SOME v => v
		val var1 = case !(BoolInfo.var bi1) of 
			       NONE => raise WRONG_VAR
			     | SOME v => v
		val varX0 = BoolInfo.var biX0
		val varX1 = BoolInfo.var biX1
		val () = case !varX0 of
			     NONE => varX0 := SOME (var0)
			   | SOME v => if Var.equals(v,var0)
				       then ()
				       else raise WRONG_VAR
		val () = case !varX1 of
			     NONE => varX1 := SOME (var1)
			   | SOME v => if Var.equals(v,var1)
				       then ()
				       else raise WRONG_VAR
		val trX0 = BoolInfo.tr biX0
		val faX0 = BoolInfo.fa biX0
		val trX1 = BoolInfo.tr biX1
		val faX1 = BoolInfo.fa biX1
		val tr0 = BoolInfo.tr bi0
		val fa0 = BoolInfo.fa bi0
		val (tr1,fa1) = (BoolInfo.tr bi1,BoolInfo.fa bi1)
				

		val () = case (!trX0,!tr0) of
			     (NONE,SOME t') => trX0 := (SOME t')
			   | (SOME t,SOME t') => trX0 := (SOME t') (*IL.<= (t,t')*)
			   | (_,_) => () 
	
		val () = case (!faX0,!fa0) of
			     (NONE,SOME f') => faX0 := (SOME f')
			   | (SOME f,SOME f') => faX0 := (SOME f')(*IL.<= (f,f')*)
			   | (_,_) => ()

		val () = case (!trX1,!tr1) of
			     (NONE,SOME t') => trX1 := (SOME t')
			   | (SOME t,SOME t') => trX1 := (SOME t')(*IL.<= (t,t')*)
			   | (_,_) => () 

		val () = case (!faX1,!fa1) of
			     (NONE,SOME f') => faX1 := (SOME f')
			   | (SOME f,SOME f') => faX1 := (SOME f')(*IL.<= (f,f')*)
			   | (_,_) => ()
	    in
		()
	    end

	fun makeWordVariable (x,w,{args,prim,...}) = 
	    let
		fun arg i = 
		    let
			val x = Vector.sub (args,i)
		    in
			VarInfo.il (varInfo x)
		    end
		fun make (newIL,size) =
		    let
			val () = setVarInfo (x, VarInfo.new (x,SOME size))
			val () = VarInfo.joinValues (varInfo x, newIL, constants)
		    in ()
		    end

		fun makeSub size = make( IL.sub(arg 0, arg 1, size),size)
		fun makeAdd size = make( IL.add(arg 0, arg 1, size),size)
		fun makeMul (size,signed) = make( IL.mul_check(arg 0, arg 1, size,signed),size)
		fun makeNeg size = make ( IL.neg(arg 0,size),size)
		fun makeLen () = make ( IL.makeZeroMax (w), w)
		datatype z = datatype Prim.Name.t
	    in
		case Prim.name prim of
		    Word_sub size => makeSub size
		  | Word_add size => makeAdd size
		  | Word_mul (size,{signed=signed}) => makeMul (size,signed)
		  | Word_neg size => makeNeg size
		  | Vector_length => makeLen()
		  | _ => (setVarInfo (x, VarInfo.new (x, SOME w)); VarInfo.makeTop (varInfo x))
	    end



	fun visitFunction f = 
	    let
		val {args, blocks, name, ...} =
                Function.dest f
(*             val _ =
                Control.diagnostic
                (fn () => 
                 let open Layout
                 in seq [str "ILprocessing function", Func.layout name]
                 end)*)
            
		fun loop (Tree.T (Block.T {label,statements,transfer,...},
				  children),
			  ancestor') = 
		    let
			(*Diagnostics*)
		(*	val _ =
			    Control.diagnostics
			    (fn display =>
				let open Layout
				in display (seq [Label.layout label,
						 
						 str "\n"])
				end)*)
			    
			val _ = 
			    Vector.foreach (statements, fn Statement.T {var,exp,ty} =>
			      case exp of
				  Const (Const.Word wx) => 
				  (case Type.dest ty of
				      Type.Word w => Option.app (var, fn x=> (setVarInfo (x, VarInfo.new (x,SOME w)); VarInfo.setConst (varInfo x, WordX.toIntInf wx)))
				    | _ => ())
				| PrimApp pa =>
				  (case Type.dest ty of
				       Type.Word w => 
				       Option.app (var, fn x=> makeWordVariable(x,w,pa))
				     | _ =>
				       Option.app (var, fn x=>
							   case (makeBoolInfo pa) of 
							       NONE=>()
							     | SOME bi => joinBoolInfo (x, bi)))
				| _ => ())
				
			val _ = 
                      case transfer of
                         Case {test, cases, default, ...} =>
                            let
                               fun add (l, f) =
                                   let
				       val var = VarInfo.var f
                                       val facts = LabelInfo.facts (labelInfo l)
				       val existingFact = findVarInfo (!facts,var)
				       val () = case existingFact of
						    NONE => ()(*List.push (facts, f)*)
						  | SOME fact => facts := List.remove (!facts, fn fa' => VarInfo.sameVar (fa',fact))
				                  (*VarInfo.joinValues (fact, VarInfo.il f)*)
				   in
				       List.push (facts,f)
                                   end           
                               fun falseTrue () =
                                  case cases of
                                     Cases.Con v =>
                                        let
                                           fun ca i = Vector.sub (v, i)
                                        in
                                           case (Vector.length v, default) of
                                              (1, SOME l') =>
                                                 let
                                                    val (c, l) = ca 0
                                                 in
                                                    if Con.equals (c, Con.truee)
                                                       then SOME (l', l)
                                                    else SOME (l, l')
                                                 end
                                            | (2, _) =>
                                                 let
                                                    val (c, l) = ca 0
                                                    val (_, l') = ca 1
                                                 in
                                                    if Con.equals (c, Con.truee)
                                                       then SOME (l', l)
                                                    else SOME (l, l')
                                                 end
                                            | _ => NONE
                                        end
                                   | _ => NONE
			       fun makeVarInfoFromBoolInfo bi =
				   case !(BoolInfo.var bi) of
				       SOME var =>
				       let
					   val tr = !(BoolInfo.tr bi)
					   val fa = !(BoolInfo.fa bi)
					   val size = BoolInfo.size bi
					   val viTr = case tr of
							  SOME _ => SOME (VarInfo.new(var,size))
							| NONE => NONE
								  
					   val viFa = case fa of
							  SOME _ => SOME (VarInfo.new(var,size))
							| NONE => NONE
								  
					   val () = case (tr,viTr) of
							(SOME t, SOME vi) => VarInfo.joinValues (vi, t,constants)
						      | (_,_) => ()
					   val () = case (fa,viFa) of
							(SOME t,SOME vi) => VarInfo.joinValues (vi, t,constants)
						      | (_,_) => ()
				       in
					   (viTr,viFa)
				       end
				     | NONE => (NONE,NONE)
			       val (bi0,bi1) = boolInfo test
			       val (vi0T,vi0F) = makeVarInfoFromBoolInfo bi0
			       val (vi1T,vi1F) = makeVarInfoFromBoolInfo bi1
			       val () = case falseTrue() of
					    SOME (l,l') => 
					    let
						val () = Option.app (vi0T, fn t=>add(l',t))
						val () = Option.app (vi0F, fn t=>add(l,t))
						val () = Option.app (vi1T, fn t=>add(l',t))
						val () = Option.app (vi1F, fn t=>add(l,t))
					    in()
					    end
					  | NONE => ()
			       val () = case cases of
				Cases.Word (size,ws) => 
				(Vector.foreach (ws, fn (v,l) =>
				  let
				      val fact = VarInfo.new (test, SOME size)
				      val () = VarInfo.setConst(fact, WordX.toIntInf v)
				  in
				      add (l,fact)
				  end)
			       ;
			       if Vector.length ws >= 1 then
				   let
				       val (v,_) = Vector.sub (ws,0)
				       val res = removeFromBound (VarInfo.il (varInfo test),v)
				       val fact = 
					   case res of
					       NONE => NONE
					     | SOME n => 
					       let
						   val vi = VarInfo.new(test,SOME size)
						   val () = VarInfo.setValue (vi, n)(*VarInfo.joinValues (vi, n,constants)*)
						   fun visit (il,i) =
						       let
							   val (v,_) = Vector.sub(ws,i)
							   val res = removeFromBound(VarInfo.il vi,v)	     
						       in
							   case res of
							       NONE => ()
							     | SOME n => 
							       (VarInfo.setValue (vi,n)(*VarInfo.joinValues (vi,n,constants)*)
							      ; 
							      if Vector.length ws >= (i+2)
							      then visit (il,i+1)
							      else ())
						       end
						   val () = if Vector.length ws >= 2
							    then visit (VarInfo.il vi, 1)
							    else ()
						       
						       
					       in 
						   SOME vi
					       end
				   in
				       case fact of
					   SOME n => Option.app (default, fn d =>add(d,n))
					 | _ => ()
				   end
			       else ())
			      | _ => ()
				     
                            in
				()
                            end
                       | _ => ()

		
			    
			    
			(*Set up ancestor*)
			val ancestor = LabelInfo.ancestor (labelInfo label)
			val facts = LabelInfo.facts (labelInfo label)
			val _ = ancestor := ancestor'
			val ancestor' = if List.isEmpty (!facts)
					then ancestor'
					else SOME label

		    in Vector.foreach
		       (children, fn tree => loop (tree, ancestor'))
		    end
		val _ = loop (Function.dominatorTree f, NONE)
	    in ()
	    end

	    (*val () = List.foreach (functions, fn f=>visitFunction f)*)
	val () = 
	    let fun loop 0 = ()
		  | loop n = (List.foreach (functions, fn f=>(visitFunction f));propagate true; loop (n-1))
	    in loop (((List.length constants))*5)
	    end





(* *************** DEBUG ********************)

	val () =
	    List.foreach
	    (functions, fn function =>
	     let
		 val {blocks,...} = Function.dest function
		 val () = Vector.foreach (blocks, fn Block.T {statements,transfer,label,...} =>
		case transfer of
		    Arith {prim,args,success,...} =>
		    if Vector.length args >= 2 then
			let
			    val var1 = Vector.sub(args,0)
			    val var2 = Vector.sub(args,1)
			    val fact1 = findFact (SOME label,var1)
			    val fact2 = findFact (SOME label,var2)
			    val il1 = VarInfo.il fact1
			    val il2 = VarInfo.il fact2

			    fun testAdd (i1,i2,size,signed) =
				let
				    val max = IL.maxFromSize (size,{signed=signed})
				in
				    if (i1 + i2) < max 
				    then Control.diagnostics (
					 fn d=>d(Layout.record [("NONOLabel", Label.layout label),
								("I1", IL.layout il1),
								("I2", IL.layout il2)]))
				    else ()
				end
			    fun testMul (i1,i2,size,signed) =
				let
				    val max = IL.maxFromSize (size,{signed=signed})
				in
				    if (i1 * i2) < max 
				    then Control.diagnostics (
					 fn d=>d(Layout.record [("NONOLabel", Label.layout label),
								("I1", IL.layout il1),
								("I2", IL.layout il2)]))
				    else ()
				end
			    fun testSub (i1,i2,size,signed) =
				let
				    val min = IL.minFromSize (size,{signed=signed})
				in
				    if (i1 - i2) > min
				    then Control.diagnostics (
					 fn d=>d(Layout.record [("NONOUabel", Label.layout label),
								("I1", IL.layout il1),
								("I2", IL.layout il2)]))
				    else ()
				end



			    datatype z = datatype Prim.Name.t
			in
			    case (IL.value il1,IL.value il2) of
				(IL.Interval (s1e1,s1e2), IL.Interval(s2e1,s2e2)) =>
				let
				    val () = (case (s1e2,s2e2) of
						  (IL.V e1, IL.V e2) =>
						  (case Prim.name prim of
						       Word_addCheck (size,{signed=signed}) => testAdd (e1,e2,size,signed)
						     | Word_mulCheck (size,{signed=signed}) => testMul (e1,e2,size,signed)
						     | _=>()
						  )
						| _ => ())
				    val () = (case (s1e1,s2e2) of
						  (IL.V e1, IL.V e2) =>
						  (case Prim.name prim of
						       Word_subCheck (size,{signed=signed}) => testSub (e1,e2,size,signed)
						     | _=>()
						  )
						| _ => ())
				in
				    ()
				end
			      | _ => ()
			end
		    else ()

		  | _ => ()
					 )
	     in ()
	     end)

	(*************************** DEBUG END **********************)
	       

	(* Diagnostics *)
	val () =
	    Control.diagnostics
	    (fn display =>
		let open Layout
		in Vector.foreach (globals, fn Statement.T {var,exp,ty} =>
					       case var of SOME x => display(VarInfo.layout (varInfo x))
							 | NONE => display (str "VAR IS NULL"));
		   display (str "\n");
		   List.foreach
		   (functions, fn f=>
		    let 
			val {name,blocks,args,...} = Function.dest f
		    in 
			display (seq [Func.layout name,
				      str ":"]);
			Vector.foreach (args, fn (a,t)=> display (VarInfo.layout (varInfo a)));
			display (str "\n");
			Vector.foreach (blocks, fn Block.T {label,args,statements,...} =>
				  (display (seq [Label.layout label,
						 seq [str ":",
						      LabelInfo.layout (labelInfo label)]]);
				   display (str "ARGS:");
				   Vector.foreach (args, fn (a,_)=>display(seq [str "\t",
										VarInfo.layout (varInfo a)]));
				   display (str "STMS:");
				   Vector.foreach (statements, fn Statement.T {var,exp,ty} => Option.app (var, fn x => 
					case Type.dest ty of 
					    Type.Word w =>
					    display (seq [str "\n",
							  VarInfo.layout (varInfo x)])
					  | _ =>
					    let
						val (b1,b2) = boolInfo x
						val blay1 = if BoolInfo.isSomething b1
							    then BoolInfo.layout b1
							    else BoolInfo.layout b1(*Layout.empty*)
						val blay2 = if BoolInfo.isSomething b2
							    then BoolInfo.layout b2
							    else BoolInfo.layout b2(*Layout.empty*)
					    in display (seq [str "\t",
							     seq [blay1,
								  blay2]])
					    end))));
			
			display (str "\n")
		    end)

		end)
	val shrink = shrinkFunction {globals = globals}
	fun simplifyFunction f =
	    let
		val {args,blocks,mayInline,name,raises,returns,start} = Function.dest f
		val blocks = 
		    Vector.map 
		    (blocks, fn Block.T {label,args,statements,transfer} =>
                    let
			datatype z = datatype Prim.Name.t
			
			fun noChange() = (statements,transfer)
			fun simplify (prim: Type.t Prim.t,
				      x1: Var.t,
				      x2: Var.t,
				      s: WordSize.t,
				      success: Label.t) =
			    let
				val ()  = Control.diagnostics (fn d=>d(Layout.str "NONOSIMP"))
				val res = Var.newNoname()
				val stms = Vector.concat [statements,
							  Vector.new1
							  (Statement.T 
							   {exp = PrimApp {args = Vector.new2(x1,x2),
									   prim = prim,
									   targs = Vector.new0()},
							    ty = Type.word s,
							    var = SOME res})]
				val trans = Goto {args = Vector.new1 res,
						  dst = success}
			    in
				(stms,trans)
			    end
					      
			val (statements,transfer) =
			    case transfer of
				Arith {prim,args,success,...} =>
				if Vector.length args >= 2 then
				    let
					val var1 = Vector.sub(args,0)
					val var2 = Vector.sub(args,1)
					val fact1 = findFact (SOME label,var1)
					val fact2 = findFact (SOME label,var2)
					val il1 = VarInfo.il fact1
					val il2 = VarInfo.il fact2

					fun testAdd (i1,i2,size,signed) =
					    let
						val max = IL.maxFromSize (size,{signed=signed})
					    in
						if (i1 + i2) < max 
						then simplify(Prim.wordAdd size,var1,var2,size,success)
						else noChange()
					    end
					fun testMul (i1,i2,size,signed) =
					    let
						val max = IL.maxFromSize (size,{signed=signed})
					    in
						if (i1 * i2) < max 
						then simplify(Prim.wordMul (size,{signed=signed}),var1,var2,size,success)
						else noChange()
					    end
					fun testSub (i1,i2,size,signed) =
					    let
						val min = IL.minFromSize (size,{signed=signed})
					    in
						if (i1 - i2) > min
						then simplify(Prim.wordSub size,var1,var2,size,success)
						else noChange()
					    end

	
					datatype z = datatype Prim.Name.t
				    in
					case (IL.value il1,IL.value il2) of
					    (IL.Interval (s1e1,s1e2), IL.Interval(s2e1,s2e2)) =>
					    let
						val isElmsForAddMul = (case (s1e2,s2e2) of
									   (IL.V e1, IL.V e2) =>
									   SOME (e1,e2)
									 | _ => 
									   NONE
								      )

						val isElmsForSub = (case (s1e1,s2e2) of
									(IL.V e1, IL.V e2) =>
									SOME (e1,e2)
								      | _ =>
									NONE
								   )
					    in
						case Prim.name prim of
						    Word_addCheck (size,{signed=signed}) =>
						    (case isElmsForAddMul of
							 SOME (e1,e2) =>
							 testAdd (e1,e2,size,signed)
						       | NONE => noChange())
						  | Word_mulCheck (size,{signed=signed}) =>
						    (case isElmsForAddMul of
							 SOME (e1,e2) =>
							 testMul (e1,e2,size,signed)
						       | NONE => noChange())
						    
						  | Word_subCheck (size,{signed=signed}) =>
						    (case isElmsForSub of
							 SOME (e1,e2) =>
							 testSub (e1,e2,size,signed)
						       | NONE => noChange())
						    
						  | _ => noChange()
					    end
					  | _ => noChange()
				    end
				else noChange()		    

			      | _=> noChange()
					       
		    in
			Block.T {label = label,
				 args = args,
				 statements = statements,
				 transfer = transfer}
		    end)
					   
	    in
		shrink (Function.new {args = args,
				      blocks = blocks,
				      mayInline = mayInline,
                                      name = name,
                                      raises = raises,
                                      returns = returns,
                                      start = start})
	    end

	(* Analysis complate. Transform program *)
	val functions = List.map (functions, simplifyFunction)


	val program = Program.T {datatypes = datatypes,
				 globals = globals,
				 functions = functions,
				 main = main}

    in 
	program
    end
end
