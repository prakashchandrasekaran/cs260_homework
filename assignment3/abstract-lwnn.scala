import scala.io._
import scala.math._
import scala.util._
import pllab.lwnn.concrete_domains._
import pllab.lwnn.syntax._
import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.immutable.TreeMap
import scala.collection.mutable.Queue

object global {
	var integer_abstraction = "sign"
	var mod_value = 10
	var trace_option = false
	var print_ast_option = false
	var merge_of_points = new TreeMap[Int, State]()
	
	
	def print_merge_of_points {
		println(" ------------------------- MOP ---------------------------------")
		merge_of_points.keys.foreach{ program_point =>  
			var merged_state = merge_of_points(program_point)
			println("----------")
			println("[" + program_point + "]" ) 
			var temp = new TreeMap[String, String]
			merged_state.ρ.ρ foreach { case (x, a) ⇒ temp += x.x -> merged_state.σ(a).toString }
			temp.foreach {case (k, v) ⇒ println(k + " : " + v)}
		}
	}
}

// main interpreter entry point
object Lwnn {
	
  def main(args: Array[String]) {
  
    val ast = ParseL.getAST(Source.fromFile(args(0)).mkString)
    var curr_ς = State(StmtT(ast), Env(), Store(), haltK)
	
	/* worklist is a queue holds current list of items*/
	var worklist = new Queue[State]()
	worklist += curr_ς
	
	/* allstates is a set which holds all states */
	var allstates = new HashSet[State]()
	allstates += curr_ς

	if(args.length <= 1) {
		// if no option is specified, execute with default set of options
		global.integer_abstraction = "sign"
		global.trace_option = false
		global.print_ast_option = false
	}
	else {
		if (args(1).equals("--mod")) 
			global.integer_abstraction = "mod"
		else // assuming if not mod => sign
			global.integer_abstraction = "sign"
		
		if(args(1).equals("--trace") || (args.length >= 3 && args(2).equals("--trace")))
			global.trace_option = true
		
		if(args(1).equals("--ast") || (args.length >= 3 && args(2).equals("--ast")))
			global.print_ast_option = true
	}
	
	
	if (global.print_ast_option) {
		Pretty.outputAST(ast)
	}
	else {
		/* 
		 * Worklist algorithm
		 * add initial state to the worklist
		 * dequeue a state from worklist
		 * evaluate the state and add next states to the worklist if not already seen
		 * continue until worklist is empty
		 */
		while(! worklist.isEmpty) {
			curr_ς = worklist.dequeue()
			/* if trace option is Enabled */
			if(global.trace_option) 
				curr_ς.print
			/* building merge of all paths */
			curr_ς.mop_build
			var next_states = curr_ς.next
			while(! next_states.isEmpty) {
				var new_state = next_states.dequeue()
				/* checking whether new state is already seen or not */
				if( ! allstates.contains(new_state) ) {
					allstates += new_state
					worklist += new_state
				}
			}
		}
		/* printing merge of all paths */
		global.print_merge_of_points
	} 
  }
  
  
  
}

// states (with transition function)
case class State(t: Term, ρ: Env, σ: Store, κ: Kont) {

  // final state?
  def fin: Boolean =
    t.isInstanceOf[ValueT] && κ == haltK

  // expression evaluation
  private def eval(e: Exp): Value = e match {
    case Range(n1, n2) ⇒
		if(global.integer_abstraction.equals("mod")) {
			var range_values_set = HashSet[BigInt]()
			for ( i <- n1 to n2)
				range_values_set += i
			ℤMod(range_values_set)
		}
		else {
			/* global.integer_abstraction.equals("sign") == true */
			/* depending upon the range assign its equivalent sign abstraction */
			if (n1 == n2) {
				if (n1 < 0) ℤSign(Sign.N)
				else if (n1 == 0) ℤSign(Sign.O)
				else ℤSign(Sign.P)
			} 
			else {
				if (n1 > 0) ℤSign(Sign.P)
				else if (n1 >= 0) ℤSign(Sign.PO)
				else if (n2 < 0) ℤSign(Sign.N)
				else if (n2 == 0) ℤSign(Sign.ON)
				else ℤSign(Sign.PON)
			}
		}
      
    case x: Var ⇒
      σ(ρ(x)) match {
        case v: Value ⇒ v
        case _ ⇒ sys.error("inconceivable")
      }

    case Binop(op, e1, e2) ⇒
      op match {
        case ⌜+⌝ ⇒ eval(e1) + eval(e2)
        case ⌜−⌝ ⇒ eval(e1) − eval(e2)
        case ⌜×⌝ ⇒ eval(e1) × eval(e2)
        case ⌜÷⌝ ⇒ eval(e1) ÷ eval(e2)
        case ⌜=⌝ ⇒ eval(e1) ≈ eval(e2)
        case ⌜≠⌝ ⇒ eval(e1) ≠ eval(e2)
        case ⌜<⌝ ⇒ eval(e1) < eval(e2)
        case ⌜≤⌝ ⇒ eval(e1) ≤ eval(e2)
        case ⌜∧⌝ ⇒ eval(e1) ∧ eval(e2)
        case ⌜∨⌝ ⇒ eval(e1) ∨ eval(e2)
	}
	
	case _ =>
		sys.error("undefined types in eval")

  }

  // state transition function
  def next: Queue[State] = {
    var result = new Queue[State]

    t match {
      // remember to compute the collecting semantics.

      case StmtT(stmt) ⇒ stmt match {
        case e: Exp ⇒ result += (State(eval(e), ρ, σ, κ))

        case Seq(s :: rest) ⇒
          result += State(s, ρ, σ, seqK(rest, κ))

        case If(e: Exp, s1: Stmt, s2: Stmt) ⇒
          eval(e) match {
            case ℤSign(n) ⇒ {
              //State(if (n != 0) s1 else s2, ρ, σ, κ)
              if (n != Sign.O || n != Sign.EMPTY) result += State(s1, ρ, σ, κ)
              if (n == Sign.O || n == Sign.PO || n == Sign.ON || n == Sign.PON) result += State(s2, ρ, σ, κ)
              result
            }
            case z : ℤMod => {
				/* check it out */
				if ((z.n_abs.size != 0)) result += State(s1, ρ, σ, κ)
				if (z.n_abs.contains(0)) result += State(s2, ρ, σ, κ)
            result
            }
            case _ ⇒ sys.error("undefined")
          }

        case While(e: Exp, s: Stmt) ⇒
          eval(e) match {
            case ℤSign(n) ⇒ {
              if (n != Sign.O || n != Sign.EMPTY) result += State(s, ρ, σ, whileK(e, s, κ))
              if (n == Sign.O || n == Sign.PO || n == Sign.ON || n == Sign.PON) result += State(ℤSign(n), ρ, σ, κ)
              result
            }
            case z: ℤMod => {
              /** change */ if ((z.n_abs.size != 0)) result += State(s, ρ, σ, whileK(e, s, κ))
              /** change */ if (z.n_abs.contains(0)) result += State(z, ρ, σ, κ)
              result
            }
            case _ ⇒ result
          }

        case Assign(x: Var, e: Exp) ⇒
          val v = eval(e)
          result += State(v, ρ, σ + (ρ(x) → v), κ)

        case Decl(xs, s) ⇒
          val as = xs map (_ ⇒ Address())
          val vs = xs map (_ ⇒ 
			if(global.integer_abstraction.equals("sign"))
				ℤSign(Sign.O)
			else {
				ℤMod(new HashSet[BigInt]() + 0)
			}
		  )
          result += State(s, ρ ++ (xs zip as), σ ++ (as zip vs), κ)

        case _ ⇒ // only reached if empty Seq (should be impossible)
          result
		 
      }

     /*
     * The states where the Term is a value should just be put in the worklist automatically
     * without remembering them or checking to see if they've been seen before.
     */
      case ValueT(v) ⇒ κ match {
        case seqK(s :: rest, κc) ⇒
		  result += State(s, ρ, σ, seqK(rest, κc))

        case seqK(_, κc) ⇒
          result += State(v, ρ, σ, κc)

        case whileK(e, s, κc) ⇒
          eval(e) match {
			case ℤSign(n) ⇒ {
              if (n != Sign.O || n != Sign.EMPTY) result += State(s, ρ, σ, whileK(e, s, κc))
              if (n == Sign.O || n == Sign.PO || n == Sign.ON || n == Sign.PON) result += State(s, ρ, σ, κc)
              result
            }
            case z : ℤMod ⇒ {
              if ((z.n_abs.size != 0)) result += State(s, ρ, σ, whileK(e, s, κc))
              if (z.n_abs.contains( 0 )) result += State(z, ρ, σ, κc)
              result
            }
            case _ ⇒ result
          }

        case haltK ⇒
          result
    }
	
	return result
    }
  }
  
  /*
	method used in trace option to print all the states
  */
  def print {
    println(t match {
      case ValueT(v) ⇒ "value: " + v
      case StmtT(s) ⇒ "stmt: " + Pretty.stmt2str(s)
    })
	
	// println(this)
    println("Env => Store: ")
    ρ.ρ foreach { case (x, a) ⇒ println("  " + x + " ↦ " + σ(a)) }

    println("κ:")
    println(κ.toString)
    println(" ----------------------------------------------------- ")
  }
  
  /*
	mop_build method build merge of all paths map
	1) For every term (which is Stmt), we add the statement to global.merge_of_points
	with key as "Statement's Program point" and key as "State with (t, Env, Store, Kont)"
	2) When program point already added to global.merge_of_points, we merge the current State and already exixting State
	3) This method also applies the merged value to the Env.
  */
  def mop_build {
	t match {
		case StmtT(s) ⇒
			if(global.merge_of_points.contains(s.lbl)) {
				/* Merge of all paths */
				var fork1 :State = global.merge_of_points(s.lbl)
				var fork2 :State = this
				global.merge_of_points += s.lbl -> merge_states(fork1, fork2)
				/* Applying the "merged value" into current Environment */
				var store1 = fork1.σ 
				var store2 = this.σ
				store1.sto.keys.foreach(key => 
					if(store2.sto.contains(key)) 
						store2.sto += key -> merge_values(store2.sto(key), store1(key))
					else 
						store2.sto += key -> store1(key)
				)
			}
			else {
				global.merge_of_points += s.lbl -> this
			}
		case _ => // do nothing if term is not a Statement
	}
	
	/*
		merge_states takes two different states and merges them into Single state by merging their stores
	*/
	def merge_states(fork1 : State, fork2 : State) : State = {
		var merged_state : State = new State(fork1.t, fork1.ρ, merge_stores(fork1.σ, fork2.σ) , fork1.κ)
		return merged_state
	}
	
	/*
		merge_stores takes two store objects and merges them into Single Store
		if they have similar Address with different values, 
			values are merged based on merge operation defined on corresponding Value Class
	*/
	def merge_stores(store1 : Store, store2 : Store) : Store = {
		var sto:Map[Address, Value] = Map()
		sto ++= store1.sto
		store2.sto.keys.foreach(key => 
			if(sto.contains(key)) {
				sto += key -> merge_values(sto(key), store2(key))
			}
			else {
				sto += key -> store2(key)
			}
		)
		return Store(sto)
	}
	
	/*
		merge_values takes two different values and apply corresponding merge method
	*/
	def merge_values(value1 : Value, value2 : Value) : Value = {
		value1 match {
			case ℤSign(n) ⇒
				value1.merge(value2)
			case ℤMod(n) ⇒ 
				// println(" i am called for values " + value1 + " " + value2)
				value1.merge(value2)
			case _ ⇒
				
				value1
		}
	}
	
  }

  // implicit conversions
  implicit def stmt2term(s: Stmt): Term = StmtT(s)
  implicit def val2term(v: Value): Term = ValueT(v)

}