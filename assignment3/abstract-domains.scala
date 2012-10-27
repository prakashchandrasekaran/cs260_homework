package pllab.lwnn.concrete_domains

import pllab.lwnn.syntax._
import Pretty.{ stmt2str ⇒ pretty }
import scala.collection.mutable.HashSet

// DEFINES THE FOLLOWING SEMANTIC DOMAINS
//
//  t  ∈ Term = Decl + Stmt + Value    | terms
//  ρ  ∈ Env = Variable → Address      | environments
//  σ  ∈ Store = Address → Value       | stores
//  a  ∈ Address = ℕ                   | store locations
//  v  ∈ Value = ℤ                     | values
//  n  ∈ ℤ                             | integers
//  κ  ∈ Kont                          | semantic continuations

// terms (conflating decl and stmt)
sealed abstract class Term
case class StmtT(s:Stmt) extends Term
case class ValueT(v:Value) extends Term

// environment
case class Env( ρ:Map[Var, Address] = Map() ) {

  // retrieve a variable's address
  def apply( x:Var ): Address =
    ρ get x match {
      case Some(a) ⇒ a
      case None ⇒ sys.error("undefined")
    }  

  // add bindings to the environment
  def ++( bindings:List[(Var, Address)] ): Env =
    Env( ρ ++ bindings )

  // filter mapping
  def filter( f:Var => Boolean ): Env =
    Env( ρ filterKeys f )

  // get addresses in co-domain
  def addrs: Set[Address] =
    ρ.unzip._2.toSet

}

// store
case class Store( var sto:Map[Address, Value] = Map() ) {

  // retrieve an address' value
  def apply( a:Address ): Value =
    sto get a match {
      case Some(v) ⇒ v
      case None ⇒ sys.error("undefined")
    }

  // add a value to the store at the given address
  def +( av:(Address,Value) ): Store =
    Store( sto + av )

  // ditto for sequences of (address,value)
  def ++( avs:List[(Address,Value)] ): Store =
    Store( sto ++ avs )

}

// store locations
case class Address( a:Int )

// companion object for factory method
object Address {

  // helpers for generating fresh addresses
  private var aid = 0
  private def fresh(): Int =
    { aid += 1; aid }

  // generate fresh Address
  def apply(): Address =
    new Address( fresh() )
}	

// values
sealed abstract class Value {
  def + ( v:Value ): Value
  def − ( v:Value ): Value
  def × ( v:Value ): Value
  def ÷ ( v:Value ): Value
  def ≈ ( v:Value ): Value
  def ≠ ( v:Value ): Value
  def < ( v:Value ): Value
  def ≤ ( v:Value ): Value
  def ∧ ( v:Value ): Value
  def ∨ ( v:Value ): Value
  def merge (v: Value) : Value
}

case class ℤMod(n: HashSet[BigInt]) extends Value {

  val mod_value = 10;
  var n_abs : HashSet[BigInt] = n.foldLeft(HashSet[BigInt]()) ((res, curr) => res += (curr.mod(mod_value)))
  
  
  override def toString = {
	var result_str : String = ""
	n_abs.foldLeft(List[BigInt]()) { 
		(r,c) =>
			val (front, back) = r.span(_ < c)
			front ::: c :: back
	}.foreach( x => result_str += x + " " )
	result_str
  }
  
  
  def merge ( v:Value ) = v match {
    case z : ℤMod ⇒ ℤMod(n ++= z.n)
	case _ ⇒ ℤMod(new HashSet[BigInt]())
  }
  
  def + ( v:Value ) = v match {
	case z : ℤMod ⇒ ℤMod(n_abs.foldLeft(HashSet[BigInt]()) ((res, curr) => res ++= z.n_abs.foldLeft(HashSet[BigInt]()) ((res2, curr2) => res2 += (curr + curr2))))
	case _ ⇒ ℤMod(new HashSet[BigInt]()) // sys.error("undefined")
  }
  def − ( v:Value ) = v match {
	case z : ℤMod ⇒ ℤMod(n_abs.foldLeft(HashSet[BigInt]()) ((res, curr) => res ++= z.n_abs.foldLeft(HashSet[BigInt]()) ((res2, curr2) => res2 += (curr + 10 - curr2))))
	// case z : ℤMod ⇒ ℤMod(n_abs.foldLeft(HashSet[BigInt]()) ((res, curr) => res ++= z.n_abs.foldLeft(HashSet[BigInt]()) ((res2, curr2) => res2 += (curr - curr2))))
	case _ ⇒ ℤMod(new HashSet[BigInt]()) // sys.error("undefined")
  }
  def × ( v:Value ) = v match {
	case z : ℤMod ⇒ ℤMod(n_abs.foldLeft(HashSet[BigInt]()) ((res, curr) => res ++= z.n_abs.foldLeft(HashSet[BigInt]()) ((res2, curr2) => res2 += (curr * curr2))))
	case _ ⇒ ℤMod(new HashSet[BigInt]()) // sys.error("undefined")
  }
  def ÷ ( v:Value )= v match {
	case z : ℤMod ⇒ 
	if(z.n_abs.size == 1 && z.n_abs.contains(0)) {
		ℤMod(new HashSet[BigInt]()) //sys.error("undefined")
	}
	else {
		ℤMod(n_abs.foldLeft(HashSet[BigInt]()) ((res, curr) => res ++= z.n_abs.foldLeft(HashSet[BigInt]()) ((res2, curr2) => if(curr2 != 0) res2 += (curr / curr2) else res2)))
			/*
				ℤMod(
					n_abs.foldLeft(HashSet[Int]()) ((res, curr) => 
								res ++= z.n_abs.foldLeft(HashSet[Int]()) ((res2, curr2) => 
									if(curr2 != 0) res2 += (curr / curr2) else res2)
						)
					)
			*/
	}
	case _ ⇒ ℤMod(new HashSet[BigInt]())
  }
  def ≈ ( v:Value )= v match {
	case z : ℤMod  ⇒ 
		if (n_abs.size == 0 && z.n_abs.size == 0)
			ℤMod(new HashSet[BigInt]() + 1) 
		else if ((n_abs.forall(x => ! z.n_abs.contains(x)))) 
			ℤMod((new HashSet[BigInt]() + 0)) 
		else 
			ℤMod((new HashSet[BigInt]() + 0) + 1)
	case _ ⇒ ℤMod(new HashSet[BigInt]())
  }
  def ≠ ( v:Value ) = v match {
	case z : ℤMod  ⇒ 
		if (n_abs.size == 0 && z.n_abs.size == 0)
			ℤMod(new HashSet[BigInt]() + 0) 
		else if ((n_abs.forall(x => ! z.n_abs.contains(x)))) 
			ℤMod((new HashSet[BigInt]() + 1)) 
		else 
			ℤMod((new HashSet[BigInt]() + 0) + 1)
	case _ ⇒ ℤMod(new HashSet[BigInt]())
  }
  def < ( v:Value )= v match {
	case z : ℤMod  ⇒ 
		// if(n_abs.forall(x => z.n_abs.forall(x2 => (x < x2)))) ℤMod((new HashSet[BigInt]() + 0) + 1) else ℤMod(new HashSet[BigInt]() + 0)
		if (n_abs.size == 0 && z.n_abs.size == 0)
			ℤMod(new HashSet[BigInt]() + 0)
		else 
			ℤMod((HashSet[BigInt](0,1)))
	case _ ⇒ ℤMod(new HashSet[BigInt]())
  }
  def ≤ ( v:Value )= v match {
	case z : ℤMod  ⇒ 
		// if(n_abs.forall(x => z.n_abs.forall(x2 => (x <= x2)))) ℤMod((new HashSet[BigInt]() + 0) + 1) else ℤMod(new HashSet[BigInt]() + 0)
		if (n_abs.size == 0 && z.n_abs.size == 0)
			ℤMod(new HashSet[BigInt]() + 1)
		else 
			ℤMod((new HashSet[BigInt]() + 0) + 1)
	case _ ⇒ ℤMod(new HashSet[BigInt]())
  }
  def ∧ ( v:Value )= v match {
	case z : ℤMod  ⇒ 
		if(n_abs.contains(0) || z.n_abs.contains(0))
			ℤMod((new HashSet[BigInt]() + 0) + 1)
		else
			ℤMod((new HashSet[BigInt]() + 1))
	case _ ⇒ ℤMod(new HashSet[BigInt]())
  }
  def ∨ ( v:Value )= v match {
	case z : ℤMod  ⇒ 
		if(! n_abs.contains(0) || ! z.n_abs.contains(0))
			ℤMod((new HashSet[BigInt]() + 1))
		else
			ℤMod((new HashSet[BigInt]() + 0) + 1)
	case _ ⇒ ℤMod(new HashSet[BigInt]())
  }
}

/**
* Sign in an Enumeration for all abstract signs
* P => Positive => {+}
* N => Negative => {-}
* O => Zero => {0}
* PO => Positive and Zero => {+, 0}
* PN => Positive and Negative => {+,-}
* ON => Zero and Negative => {0, -}
* PON => Positive, Zero and Negative => {+, 0, -}
*/
object Sign extends Enumeration {
     type Sign = Value
	 val P, O, N, PO, PN, ON, PON, EMPTY = Value
}

import Sign._

// abstract integers - signs
case class ℤSign(sign:Sign) extends Value {
	  
  def + ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case P | O | PO ⇒ ℤSign(P)
				case N | PN | ON | PON ⇒ ℤSign(PON)
			}
			case N ⇒ sign2 match {
				case N | O | ON ⇒ ℤSign(N)
				case P | PO | PN | PON ⇒ ℤSign(PON)
			}
			case O ⇒ sign2 match {
				case P ⇒ ℤSign(N)
				case N ⇒ ℤSign(P)
				case O ⇒ ℤSign(O)
				case PO ⇒ ℤSign(ON)
				case PN ⇒ ℤSign(PN)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PON)
			}
			case PO ⇒ sign2 match {
				case N | PN | ON | PON ⇒ ℤSign(PON)
				case O | PO | P ⇒ ℤSign(PO)
			}
			case PN ⇒ sign2 match {
				case P | N | PN | PON | ON | PO ⇒ ℤSign(PON)
				case O ⇒ ℤSign(PN)
			}
			case ON ⇒ sign2 match {
				case P | PO | PON | PN ⇒ ℤSign(PON)
				case O | ON | N ⇒ ℤSign(ON)
			}
			case PON ⇒ sign2 match {
				case P | O | N | PN | PO | ON | PON ⇒ ℤSign(PON)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }
  
  def merge ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case O | PO ⇒ ℤSign(PO)
				case N | PN ⇒ ℤSign(PN)
				case ON | PON ⇒ ℤSign(PON)
			}
			case N ⇒ sign2 match {
				case N ⇒ ℤSign(N)
				case O | ON ⇒ ℤSign(ON)
				case P | PN  ⇒ ℤSign(PN)
				case PO | PON ⇒ ℤSign(PON)
			}
			case O ⇒ sign2 match {
				case O ⇒ ℤSign(O)
				case N | ON ⇒ ℤSign(ON)
				case P | PO  ⇒ ℤSign(PO)
				case PN | PON ⇒ ℤSign(PON)
			}
			case PO ⇒ sign2 match {
				case N | PN | ON | PON ⇒ ℤSign(PON)
				case O | PO | P ⇒ ℤSign(PO)
			}
			case PN ⇒ sign2 match {
				case P | N | PN  ⇒ ℤSign(PN)
				case O | PON | ON | PO ⇒ ℤSign(PON)
			}
			case ON ⇒ sign2 match {
				case P | PO | PON | PN ⇒ ℤSign(PON)
				case O | ON | N ⇒ ℤSign(ON)
			}
			case PON ⇒ sign2 match {
				case P | O | N | PN | PO | ON | PON ⇒ ℤSign(PON)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined -- " + v)
  }
  
  def − ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case N | O | ON ⇒ ℤSign(P)
				case P | PN | PO | PON ⇒ ℤSign(PON)
			}
			case N ⇒ sign2 match {
				case P | O | PO ⇒ ℤSign(N)
				case N | ON | PN | PON ⇒ ℤSign(PON)
			}
			case O ⇒ ℤSign(sign2)
			case PO ⇒ sign2 match {
				case N | ON | O  ⇒ ℤSign(PO)
				case P | N | PN | PO | PON ⇒ ℤSign(PON)
			}
			case PN ⇒ sign2 match {
				case P | N | PN | PON | ON | PO ⇒ ℤSign(PON)
				case O ⇒ ℤSign(PN)
			}
			case ON ⇒ sign2 match {
				case ON | PON | PN | N ⇒ ℤSign(PON)
				case O | PO | P ⇒ ℤSign(ON)
			}
			case PON ⇒ sign2 match {
				case P | O | N | PN | PO | ON | PON ⇒ ℤSign(PON)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }

  def × ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case N ⇒ ℤSign(N)
				case O ⇒ ℤSign(O)
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(PN)
				case ON ⇒ ℤSign(ON)
				case PON ⇒ ℤSign(PON)
			}
			case N ⇒ sign2 match {
				case P ⇒ ℤSign(N)
				case N ⇒ ℤSign(P)
				case O ⇒ ℤSign(O)
				case PO ⇒ ℤSign(ON)
				case PN ⇒ ℤSign(PN)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PON)
			}
			case O ⇒ ℤSign(O)
			case PO ⇒ sign2 match {
				case O ⇒ ℤSign(O)
				case N | ON ⇒ ℤSign(ON)
				case P | PO ⇒ ℤSign(PO)
				case PON | PN ⇒ ℤSign(PON)
			}
			case PN ⇒ sign2 match {
				case P | N | PN ⇒ ℤSign(PN)
				case PON | ON | PO ⇒ ℤSign(PON)
				case O ⇒ ℤSign(O)
			}
			case ON ⇒ sign2 match {
				case O ⇒ ℤSign(O)
				case N | ON ⇒ ℤSign(PO)
				case P | PO ⇒ ℤSign(ON)
				case PON | PN ⇒ ℤSign(PON)
			}
			case PON ⇒ sign2 match {
				case P | O | N | PN | PO | ON | PON ⇒ ℤSign(PON)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }

  def ÷ ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case N ⇒ ℤSign(N)
				case O ⇒ ℤSign(EMPTY) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(P)
				case PN ⇒ ℤSign(PN)
				case ON ⇒ ℤSign(N)
				case PON ⇒ ℤSign(PN)
			}
			case N ⇒ sign2 match {
				case P ⇒ ℤSign(N)
				case N ⇒ ℤSign(P)
				case O ⇒ ℤSign(EMPTY) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(N)
				case PN ⇒ ℤSign(PN)
				case ON ⇒ ℤSign(P)
				case PON ⇒ ℤSign(PN)
			}
			case O ⇒ ℤSign(O)
			case PO ⇒ sign2 match {
				case P ⇒ ℤSign(PO)
				case N ⇒ ℤSign(ON)
				case O ⇒ ℤSign(EMPTY) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(P)
				case PN ⇒ ℤSign(PN)
				case ON ⇒ ℤSign(N)
				case PON ⇒ ℤSign(PN)
			}
			case PN ⇒ sign2 match {
				case P | N | PN | PON | ON | PO ⇒ ℤSign(PN)
				case O ⇒ ℤSign(EMPTY) // sys.error(" divide by zero error")
			}
			case ON ⇒ sign2 match {
				case P ⇒ ℤSign(ON)
				case N ⇒ ℤSign(PO)
				case O ⇒ ℤSign(EMPTY) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(N)
				case PN ⇒ ℤSign(PN)
				case ON ⇒ ℤSign(P)
				case PON ⇒ ℤSign(PN)
		}
			case PON ⇒ sign2 match {
				case P | N | PN ⇒ ℤSign(PON)
				case O ⇒ ℤSign(EMPTY) // sys.error(" divide by zero error")
				case PO | ON | PON ⇒ ℤSign(PN)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }

  def ≈ ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case P ⇒ ℤSign(PO)
				case N ⇒ ℤSign(O)
				case O ⇒ ℤSign(O) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(PO)
				case ON ⇒ ℤSign(O)
				case PON ⇒ ℤSign(PO)
			}
			case N ⇒ sign2 match {
				case P ⇒ ℤSign(O)
				case N ⇒ ℤSign(PO)
				case O ⇒ ℤSign(O) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(O)
				case PN ⇒ ℤSign(PO)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
			}
			case O ⇒ sign2 match {
				case P ⇒ ℤSign(O)
				case N ⇒ ℤSign(O)
				case O ⇒ ℤSign(P) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(O)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
			}
			case PO ⇒ sign2 match {
				case P ⇒ ℤSign(PO)
				case N ⇒ ℤSign(O)
				case O ⇒ ℤSign(PO) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(PO)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
			}
			case PN ⇒ sign2 match {
				case P | N | PN | PON | ON | PO ⇒ ℤSign(PO)
				case O ⇒ ℤSign(O) // sys.error(" divide by zero error")
			}
			case ON ⇒ sign2 match {
				case P ⇒ ℤSign(O)
				case N ⇒ ℤSign(PO)
				case O ⇒ ℤSign(PO) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(PO)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
		}
			case PON ⇒ sign2 match {
				case O | PO | ON | PON | P | N | PN ⇒ ℤSign(PON)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }
  
  def ≠ ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case P ⇒ ℤSign(PO)
				case N ⇒ ℤSign(P)
				case O ⇒ ℤSign(P) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(PO)
				case ON ⇒ ℤSign(P)
				case PON ⇒ ℤSign(PO)
			}
			case N ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case N ⇒ ℤSign(PO)
				case O ⇒ ℤSign(P) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(P)
				case PN ⇒ ℤSign(PO)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
			}
			case O ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case N ⇒ ℤSign(P)
				case O ⇒ ℤSign(O) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(P)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
			}
			case PO ⇒ sign2 match {
				case P ⇒ ℤSign(PO)
				case N ⇒ ℤSign(P)
				case O ⇒ ℤSign(PO) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(PO)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
			}
			case PN ⇒ sign2 match {
				case P | N | PN | PON | ON | PO ⇒ ℤSign(PO)
				case O ⇒ ℤSign(P) // sys.error(" divide by zero error")
			}
			case ON ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case N ⇒ ℤSign(PO)
				case O ⇒ ℤSign(PO) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(PO)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
		}
			case PON ⇒ sign2 match {
				case O | PO | ON | PON | P | N | PN ⇒ ℤSign(PO)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }
  
  def < ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case N | O | ON ⇒ ℤSign(O)
				case _ ⇒ ℤSign(PO)
			}
			case N ⇒ sign2 match {
				case P | PO | O ⇒ ℤSign(P)
				case _ ⇒ ℤSign(PO)
			}
			case O ⇒ sign2 match {
				case N | O ⇒ ℤSign(O)
				case P ⇒ ℤSign(P)
				case _ ⇒ ℤSign(PON)
			}
			case PO ⇒ sign2 match {
				case N ⇒ ℤSign(O)
				case _ ⇒ ℤSign(PON)
			}
			case PN ⇒ ℤSign(PO)
			case ON ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case _ ⇒ ℤSign(PO)
			}
			case PON ⇒ ℤSign(PO)
		}
		case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }
	
	def ≤ ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case N | O | ON ⇒ ℤSign(O)
				case _ ⇒ ℤSign(PO)
			}
			case N ⇒ sign2 match {
				case P | PO | O ⇒ ℤSign(P)
				case _ ⇒ ℤSign(PON)
			}
			case O ⇒ sign2 match {
				case N ⇒ ℤSign(O)
				case P | O | PO ⇒ ℤSign(P)
				case _ ⇒ ℤSign(PO)
			}
			case PO ⇒ sign2 match {
				case N ⇒ ℤSign(O)
				case _ ⇒ ℤSign(PO)
			}
			case PN ⇒ ℤSign(PO)
			case ON ⇒ sign2 match {
				case P | O ⇒ ℤSign(P)
				case _ ⇒ ℤSign(PO)
			}
			case PON ⇒ ℤSign(PO)
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }

  def ∧ ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case N ⇒ ℤSign(P)
				case O ⇒ ℤSign(O) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(P)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
			}
			case N ⇒ sign2 match {
				case P ⇒ ℤSign(P)
				case N ⇒ ℤSign(P)
				case O ⇒ ℤSign(O) // sys.error(" divide by zero error")
				case PO ⇒ ℤSign(PO)
				case PN ⇒ ℤSign(P)
				case ON ⇒ ℤSign(PO)
				case PON ⇒ ℤSign(PO)
			}
			case O ⇒ sign2 match {
				case _ ⇒ ℤSign(O)
			}
			case PO ⇒ sign2 match {
				case O ⇒ ℤSign(O) // sys.error(" divide by zero error")
				case _ ⇒ ℤSign(PO)
			}
			case PN ⇒ sign2 match {
				case P | N | PN ⇒ ℤSign(P)
				case PON | ON | PO ⇒ ℤSign(PO) 
				case O ⇒ ℤSign(O) 
			}
			case ON ⇒ sign2 match {
				case O ⇒ ℤSign(O) 
				case _ ⇒ ℤSign(PO)
		}
			case PON ⇒ sign2 match {
				case O ⇒ ℤSign(O) 
				case _ ⇒ ℤSign(PO)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }
  
  
  def ∨ ( v:Value ) = v match {
    case ℤSign(sign2) ⇒ sign match {
			case P ⇒ sign2 match {
				case _ ⇒ ℤSign(P)
			}
			case N ⇒ sign2 match {
				case _ ⇒ ℤSign(P)
			}
			case O ⇒ sign2 match {
				case PON | PO | ON ⇒ ℤSign(PO)
				case O ⇒ ℤSign(O)
				case _ ⇒ ℤSign(P)
			}
			case PO ⇒ sign2 match {
				case P | N | PN ⇒ ℤSign(P)
				case _ ⇒ ℤSign(PO)
			}
			case PN ⇒ sign2 match {
				case _ ⇒ ℤSign(P)
			}
			case ON ⇒ sign2 match {
				case P | N | PN ⇒ ℤSign(P) 
				case _ ⇒ ℤSign(PO)
		}
			case PON ⇒ sign2 match {
				case P | N | PN ⇒ ℤSign(P) 
				case _ ⇒ ℤSign(PO)
			}
		}
	case _ ⇒ ℤSign(EMPTY) // sys.error("undefined")
  }
  

  override def toString = sign match {
	case P ⇒ "+"
	case N ⇒ "-"
	case O ⇒ "0"
	case PO ⇒ "+ 0"
	case PN ⇒ "+ -"
	case ON ⇒ "0 -"
	case PON ⇒ "+ 0 -"
	case EMPTY ⇒ "EMPTY"
  }
}

// semantic continuations
sealed abstract class Kont

case object haltK extends Kont {
  override def toString = "— haltK"
}

case class seqK(ss:List[Stmt], κ:Kont) extends Kont {
  override def toString = (if (!ss.isEmpty) "— " + pretty(Seq(ss)) + "\n" else "— seq □\n") + κ
}

case class whileK(e:Exp, s:Stmt, κ:Kont) extends Kont {
  override def toString = "— while (" + pretty(e) + ") { " + pretty(s) + " }\n" + κ
}

