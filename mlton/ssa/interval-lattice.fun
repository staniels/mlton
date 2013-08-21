functor IntervalLattice (S: INTERVAL_LATTICE_STRUCTS) =
struct

open S

exception LATTICE_IS_BOT
exception TRUE_IS_DEAD
exception FALSE_IS_DEAD
exception WORDSIZE_NONE

datatype t = T of {value: value ref,
		   size: WordSize.t option}
and value = 
    BOT
  | TOP
  | Interval of elm * elm
and elm =
    MIN
  | MAX
  | V of IntInf.t

fun new (w): t = T {value = ref BOT,
		    size = w}

fun value (T {value,...}) = !value
fun size (T {size,...}) = size
fun setValue (T {value,...}, newVal) = value := newVal



fun elmEq (elm1,elm2) =
    case (elm1,elm2) of
	(MIN,MIN) => true
      | (MAX,MAX) => true
      | (V e1, V e2) => e1=e2
      | _ => false

fun equals (T {value=value1,size=size1}, T {value=value2,size=size2}) = 
    (case (size1,size2) of 
	 (NONE,NONE) => true
       | (SOME s1, SOME s2) => WordSize.equals(s1,s2)
       | _ => false)
    andalso
    (case (!value1,!value2) of
	      (TOP,TOP) => true
	    | (BOT,BOT) => true
	    | (Interval(s1e1,s1e2), Interval(s2e1,s2e2)) =>
	      elmEq (s1e1,s2e1) andalso elmEq (s1e2,s2e2)
	    | (_,_) => false)

fun minFromSize (size,signed) =
    WordSize.min (size,signed)

fun maxFromSize (size,signed) =
    WordSize.max (size,signed)

fun setLowerElm (T {value,size}, e) = 
    case size of
	NONE => ()(*raise WORDSIZE_NONE*)
      | SOME si =>
	let 
	    val element = case e of
			      MIN => MIN
			    | MAX => MAX
			    | V e' => if e' <= minFromSize(si,{signed=true})
				      then MIN
				      else V e'
	in 
	    case !value of
		Interval (_,e2) => value := Interval (element,e2)
	      | _ => ()
	end
    
fun setHigherElm (T {value,size}, e) = 
    case size of
	NONE => ()(*raise WORDSIZE_NONE*)
      | SOME si =>
	let 
	    val element = case e of
			      MIN => MIN
			    | MAX => MAX
			    | V e' => if e' >= maxFromSize(si,{signed=true})
				      then MAX
				      else V e'
	in 
	    case !value of
		Interval (e1,_) => value := Interval (e1,element)
	      | _ => ()
	end
	
fun elmMinusOne (e,size,signed) =
    case e of
	MIN => MIN
      | MAX => MAX
      | (V e') => 
	let 
	    val res = e'-1
	in
	    if res < minFromSize(size,signed) 
	    then MIN
	    else V res
	end

fun elmPlusOne (e,size,signed) =
    case e of
	MIN => MIN
      | MAX => MAX
      | (V e') => 
	let
	    val res = e'+1
	in if res > maxFromSize(size,signed)
	   then MAX
	   else V res
	end

fun elmMinus (e1,e2,size,signed) =
    case (e1,e2) of
	(V e1', V e2') =>
	let
	    val res = (e1')-(e2')
	in 
	    if res < minFromSize(size,signed)
	    then MIN 
	    else V res
	end
      | (MAX,MAX) => MAX
      | _ => MIN

fun elmAdd (e1,e2,size,signed) =
    case (e1,e2) of
	(V e1', V e2') =>
	let
	    val res = (e1')+(e2')
	in 
	    if res > maxFromSize(size,signed)
	    then MAX 
	    else V res
	end
      | (MIN,MIN) => MIN
      | _ => MAX

fun elmMul (e1,e2,size,signed) =
    case (e1,e2) of
	(V e1', V e2') =>
	let
	    val res = (e1')*(e2')
	in 
	    if res > maxFromSize(size,signed)
	    then MAX 
	    else V res
	end
      | (MIN,MIN) => MIN
      | _ => MAX


fun addOneLow (T {value,size}) = 
    let 
	val value = case (!value,size) of
			(Interval (e1,e2), SOME s) =>
			ref (Interval (elmPlusOne (e1,s,{signed=true}),e2))
		      | (_,_) => value
    in 
	T ({value = value,
	    size = size})
    end

fun subOneHigh (T {value,size}) = 
    let
	val value = case (!value,size) of
			(Interval (e1,e2), SOME s) =>
			ref (Interval (e1,elmMinusOne (e2,s,{signed=true})))
		      | (_,_) => value
    in
	T ({value = value,
	    size = size})
    end

fun isTop (T {value,...}) = 
    case !(value) of
	TOP => true
      | _ => false

fun isBottom (T {value,...}) =
    case !(value) of
	BOT => true
      | _ => false

fun makeTop (T {value,...}) =
    value := TOP

fun normalize v =
    case v of
	Interval (MIN,MAX) => TOP
      | n => n

fun makeMin (T {value,...}) =
    case !value of
	Interval (e1,e2) => value := normalize(Interval (MIN,e2))
      | _ => ()

fun makeMax (T {value,...}) =
    case !value of
	Interval (e1,e2) => value := normalize(Interval (e1,MAX))
      | _ => ()

fun elmToString elm =
    case elm of 
	MIN => "MIN"
      | MAX => "MAX"
      | (V e') => (IntInf.toString e')

fun elmLt (elm1, elm2) = 
    case (elm1,elm2) of
	(MIN,MIN) => false
      | (MAX,MAX) => false
      | (MIN,_) => true
      | (_,MAX) => true
      | (V e1, V e2) => (e1 < e2)
      | _ => false



fun sizeString size =
    case size of
	NONE => ""
      | SOME s => "{"^(WordSize.toString s)^"}"

fun toString (T {value,size}) =
    case !(value) of
	BOT => (sizeString size)^"BOT"
      | TOP => (sizeString size)^"TOP"
      | Interval (e1,e2) => (sizeString size)^"["^(elmToString e1)^";"^(elmToString e2)^"]"

val layout = Layout.str o toString

fun setConstant (T {value,...}, c) =
    value := Interval (V c, V c)


fun <= (T {value=value1,...}, T {value=value2,...}) =
    case (!value1, !value2) of
	(_,TOP) => value1 := TOP
      | (BOT,Interval (e1,e2)) => value1 := Interval(e1,e2)
      | (Interval (s1e1,s1e2), Interval (s2e1, s2e2)) =>
	let 
	    val newe1 = if elmLt (s1e1,s2e1) 
			then s1e1
			else s2e1
	    val newe2 = if elmLt (s1e2,s2e2)
			then s2e2
			else s1e2
	in 
	    value1 := (normalize(Interval (newe1,newe2)))
	end
      | (_,BOT) => ()
      | (TOP,_) => ()
	
fun intersect (Interval (s1e1,s1e2), Interval (s2e1,s2e2)) =
    let 
	val newE1 = if elmLt (s1e1,s2e1) 
		    then s2e1
		    else s1e1
	val newE2 = if elmLt (s1e2,s2e2)
		    then s1e2
		    else s2e2
    in 
	normalize(Interval (newE1, newE2))
    end
  | intersect (_,TOP) = TOP
  | intersect (TOP,_) = TOP
  | intersect (_,_) = raise LATTICE_IS_BOT


fun newBoundLT (T {value=value1,...}, T {value=value2,...}, size,signed) = 
    let
	val (v1,v2) = case (!value1,!value2) of
		    (v1',BOT) => (v1',v1')
		  | (i1 as Interval (s1e1,s1e2), i2 as Interval (s2e1,s2e2)) =>
		    let 
			val newI1 = 
			    if elmLt (s2e2, s1e1) orelse elmEq (s1e1,s1e2)
			    then i1
			    else intersect (i1,Interval (s1e1, elmMinusOne (s2e2,size,signed)))
			val newI2 = 
			    if elmLt (s1e2,s2e1) orelse elmEq (s1e1,s1e2)
			    then i1
			    else intersect (i1,Interval (s2e1, s1e2))
		    in 
			(newI1,newI2)
		    end
		  | (_,Interval (e1,e2)) => 
		    (Interval (MIN, elmMinusOne (e2,size,signed)),
		     Interval (e1,MAX))
		  | (Interval (e1,e2), TOP) => 
		    (Interval (e1,e2),
		     Interval (e1,e2))
		  | (_,TOP) => (TOP,TOP)
    in
	(T {value=ref (normalize(v1)),
	   size=SOME size},
	 T {value=ref (normalize(v2)),
	    size=SOME size})
    end

fun newBoundGTEQ (T {value=value1,...}, T {value=value2,...}, size,signed) = 
    let
	val (v1,v2) = case (!value1,!value2) of
		    (v1',BOT) => (v1',v1')
		  | (i1 as Interval (s1e1,s1e2), i2 as Interval (s2e1,s2e2)) =>
		    let 
			val newI1 = 
			    if elmLt (s1e2,s2e1) orelse elmEq (s1e1,s1e2)
			    then i1
			    else intersect (i1,Interval (s2e1, s1e2))
			val newI2 = 
			    if elmLt (s2e2, s1e1) orelse elmEq (s1e1,s1e2)
			    then i1
			    else intersect (i1,Interval (s1e1, elmMinusOne (s2e2,size,signed)))
		    in 
			(newI1,newI2)
		    end
		  | (_,Interval (e1,e2)) => 
		    (Interval (e1,MAX),
		     Interval (MIN,elmMinusOne (e2,size,signed)))
		  | (Interval (e1,e2), TOP) => 
		    (Interval (e1,e2),
		     Interval (e1,e2))
		  | (_,TOP) => (TOP,TOP)
    in
	(T {value=ref (normalize(v1)),
	   size=SOME size},
	 T {value=ref (normalize(v2)),
	    size=SOME size})
    end

fun sub_check (T {value=value1,...}, T {value=value2,...}, size,sign) = 
    let
	val newIL = case (!value1,!value2) of
			(Interval (s1e1,s1e2),Interval(s2e1,s2e2)) =>
			Interval (elmMinus (s1e1,s2e2,size,{signed=sign}), elmMinus (s1e2,s2e1,size,{signed=sign}))
		      | (_,_) => TOP
    in
	T {value=ref (normalize(newIL)),
	   size=SOME size}
    end



fun add_check (T {value=value1,...}, T {value=value2,...}, size,sign) = 
    let
	val newIL = case (!value1,!value2) of
			(Interval (s1e1,s1e2),Interval(s2e1,s2e2)) =>
			Interval (elmAdd (s1e1,s2e1,size,{signed=sign}), elmAdd (s1e2,s2e2,size,{signed=sign}))
		      | (_,_) => TOP
    in
	T {value=ref (normalize(newIL)),
	   size=SOME size}
    end


fun mul_check (T {value=value1,...}, T {value=value2,...}, size,sign) = 
    let
	val newIL = case (!value1,!value2) of
			(Interval (s1e1,s1e2),Interval(s2e1,s2e2)) =>
			Interval (elmMul (s1e1,s2e1,size,{signed=sign}), elmMul (s1e2,s2e2,size,{signed=sign}))
		      | (_,_) => TOP
    in
	T {value=ref (normalize(newIL)),
	   size=SOME size}
    end


fun add (i1,i2,size) = add_check (i1,i2,size,true)
fun sub (i1,i2,size) = sub_check (i1,i2,size,true)
fun mul (i1,i2,size) = mul_check (i1,i2,size,true)

fun neg (T {value,...},size) = 
    let 
	val newIL = case !value of
			Interval (e1,e2) =>
			Interval (elmMinus (V 0,e2,size,{signed=true}), elmMinus(V 0,e1,size,{signed=true}))
		      | _ => TOP
    in
	T {value = ref (normalize(newIL)),
	   size = SOME size}
    end

fun makeZeroMax size =
    T {value = ref (Interval(V 0, MAX)),
       size = SOME size}

end


