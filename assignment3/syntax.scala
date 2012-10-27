package pllab.lwnn.syntax

import java.io._
import scala.io._

//---------- AST ----------

sealed abstract class AST {
  val lbl = AST.id() // node label
}

object AST {
  // create unique node labels
  var gen = 0
  def id(): Int = { gen += 1; gen }
}

// Decl made a subclass of Stmt for convenience, though technically
// they are distinct

// statements
sealed abstract class Stmt extends AST
case class Decl(xs:List[Var], s:Stmt) extends Stmt
case class Seq(ss:List[Stmt]) extends Stmt
case class If(e:Exp, s1:Stmt, s2:Stmt) extends Stmt
case class While(e:Exp, s:Stmt) extends Stmt
case class Assign(x:Var, e:Exp) extends Stmt
case class Break() extends Stmt
case class Continue() extends Stmt

// expressions
sealed abstract class Exp extends Stmt
case class Range(n1:BigInt, n2:BigInt) extends Exp
case class Var(x:String) extends Exp
case class Binop(op:Bop, e1:Exp, e2:Exp) extends Exp
case class Strs(strs:Set[String]) extends Exp

// binary operators
sealed abstract class Bop
case object ⌜+⌝ extends Bop
case object ⌜−⌝ extends Bop
case object ⌜×⌝ extends Bop
case object ⌜÷⌝ extends Bop
case object ⌜=⌝ extends Bop
case object ⌜≠⌝ extends Bop
case object ⌜<⌝ extends Bop
case object ⌜≤⌝ extends Bop
case object ⌜∧⌝ extends Bop
case object ⌜∨⌝ extends Bop

//---------- PARSER ----------

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._

object ParseL extends StandardTokenParsers with PackratParsers {
  type P[T] = PackratParser[T]

  // reserved keywords 
  lexical.reserved += ( "decl", "in", "if", "else", "while", "self",
		        "break", "continue" )

  lexical.delimiters += ( "+", "-", "*", "/", "&", "|", "=", "!=",
			 "<", "<=", "{", "}", "(", ")", ":=", ";",
			 ",", "[", "]", ".", ":", "..", "=>", "##" )
  
  // take the program as a string and return the corresponding AST
  // (or exit with an error message)
  def getAST(program:String) = {
    // strip out comments
    val commentR = """##((#?[^#]+)*)##""".r
    val prog = commentR.replaceAllIn( program, "" )

    // parse the program
    val lexer = new lexical.Scanner(prog)
    val result = phrase(declP)(lexer)
    
    // return result or a useful error message
    result match {
      case Success(ast,_) => 
	ast

      case NoSuccess(msg,next) => { 
	println("Parse error: " + msg)
	println("At line " + next.pos.line + ", column " + next.pos.column)
	println(next.pos.longString)
	sys.exit(1) 
      }
    }
  }

  lazy val declP: P[Decl] =
    "decl" ~> rep1sep(varP, ",") ~ ("in" ~> stmtP) ^^
    { case xs ~ s ⇒ Decl(xs, s) }

  lazy val stmtP: P[Stmt] =
    seqP

  lazy val seqP: P[Stmt] =
    repsep(cmdP, ";") ^^ ( (ss) ⇒ if (ss.length == 1) ss.head else Seq(ss) )

  lazy val cmdP: P[Stmt] = (
      ifP
    | whileP
    | breakP
    | contP
    | assignP
    | expP
  )

  lazy val expP: P[Exp] = 
    ( binopP | E )

  lazy val binopP: P[Binop] =
    E ~ bopP ~ expP ^^
    { case e1 ~ bop ~ e2 ⇒ Binop(bop, e1, e2) }

  lazy val bopP: P[Bop] = (
      "+"  ^^^ ⌜+⌝
    | "-"  ^^^ ⌜−⌝
    | "*"  ^^^ ⌜×⌝
    | "/"  ^^^ ⌜÷⌝
    | "="  ^^^ ⌜=⌝
    | "!=" ^^^ ⌜≠⌝
    | "<"  ^^^ ⌜<⌝
    | "<=" ^^^ ⌜≤⌝
    | "&"  ^^^ ⌜∧⌝
    | "|"  ^^^ ⌜∨⌝
  )

  lazy val E: P[Exp] = (
      rangeP
    | strsP
    | constP
    | varP
    | "(" ~> expP <~ ")"
  )

  lazy val rangeP:P[Range] = (
    "[" ~> (numP <~ "..") ~ (numP <~ "]") ^^
    { case n1 ~ n2 ⇒ if (n1 <= n2) Range(n1, n2) 
		     else sys.error("malformed range") }
    | constP
  )

  lazy val constP:P[Range] =
    numP ^^ 
    { case n ⇒ Range(n, n) }

  lazy val numP: P[BigInt] = (
      numericLit        ^^ ((n:String) ⇒ BigInt(n))
    | "-" ~> numericLit ^^ ((n:String) ⇒ -BigInt(n))
  )

  lazy val varP: P[Var] =
    ident ^^ (Var)

  lazy val ifP: P[If] =
    "if" ~ "(" ~> expP ~ (")" ~> (("{" ~> stmtP <~ "}") | cmdP )) ~ opt("else" ~> (("{" ~> stmtP <~ "}") | cmdP)) ^^
    { case guard ~ sT ~ sFo ⇒ sFo match { 
	case Some(sF) ⇒ If(guard, sT, sF) 
        case None ⇒ If(guard, sT, Range(0, 0))
      }
    }

  lazy val whileP: P[While] =
    "while" ~ "(" ~> expP ~ (")" ~> (("{" ~> stmtP <~ "}") | cmdP)) ^^ 
    { case guard ~ body ⇒ While(guard, body) }    

  lazy val assignP: P[Assign] =
    varP ~ (":=" ~> expP) ^^ 
    { case x ~ rhs ⇒ Assign(x, rhs) }

  lazy val breakP: P[Break] =
    "break" ^^^ Break()

  lazy val contP: P[Continue] =
    "continue" ^^^ Continue()

  lazy val strsP: P[Strs] = (
    "[" ~> rep1sep(stringLit, ",") <~ "]" ^^
    { case strs ⇒ Strs(strs.toSet) }
    | stringLit ^^ 
    { case str ⇒ Strs(Set(str)) }
  )
}

//---------- PRETTY PRINT ----------

object Pretty {

  def stmt2str( s:Stmt ): String = s match {
    case Decl(xs, s) ⇒
      "decl " + (xs map stmt2str).mkString(", ") + " in " + stmt2str(s)

    case Seq(ss) ⇒
      (ss map stmt2str).mkString("; ")

    case If(e, s1, s2) ⇒
      "if (" + stmt2str(e) + ") { " + stmt2str(s1) + " } else { " + 
      stmt2str(s2) + " }"

    case While(e, s) ⇒
      "while (" + stmt2str(e) + ") { " + stmt2str(s) + " }"

    case Assign(Var(x), e) ⇒
      x + " := " + stmt2str(e)

    case _:Break ⇒
      "break"

    case _:Continue ⇒
      "continue"

    case Range(n1, n2) ⇒
      if (n1 == n2) n1.toString else "[" + n1 + ", " + n2 + "]"

    case Var(x) ⇒
      x

    case Binop(op, e1, e2) ⇒
      stmt2str(e1) + " " + op + " " + stmt2str(e2)

    case Strs(strs) ⇒
      if (strs.size == 1) strs.head else "[" + strs.mkString(",") + "]"
  }

  def outputAST(ast:AST): Unit = {
    out = new PrintWriter( 
      new BufferedWriter( 
	new FileWriter( "ast.dot" ) ) )
    
    out.println( "digraph AST {" )
    out.println( "ordering = out;" )

    dotify( ast )

    out.println( "}" )
    out.close    
  }

  var nodeid = 0
  def getid() = { nodeid += 1; nodeid }

  var out: PrintWriter = null

  def node( l:String ): Int = {
    val id = getid()
    out.println( id + " [label=\"" + l + "\"];" )
    id
  }

  def edge( e:(Int,Int) ) =
    out.println( e._1 + " -> " + e._2 )

  def edgeL( e:(Int,Int), l:String ) =
    out.println( e._1 + " -> " + e._2 + "[label=\"" + l + "\"]" )

  def dotify(ast:AST): Int = ast match {
    case Decl(xs, s) ⇒
      val cid = dotify(s)
      val id = node( "decl" )
      edge( id → cid )
      id

    case Seq(ss) ⇒
      val cids = ss map dotify
      val id = node( "seq" )
      cids map ( (i) ⇒ edge( id → i ) )
      id

    case If(e, s1, s2) ⇒
      val cidG = dotify(e)
      val cidT = dotify(s1)
      val cidF = dotify(s2)
      val id = node( "if" )
      edgeL( id → cidG,  "G" )
      edgeL( id → cidT, "T" )
      edgeL( id → cidF, "F" )
      id

    case While(e, s) ⇒
      val cidG = dotify(e)
      val cidB = dotify(s)
      val id = node( "while" )
      edgeL( id → cidG, "G" )
      edgeL( id → cidB, "B" )
      id

    case Assign(Var(x), e) ⇒
      val cid = dotify(e)
      val id = node( x + " :=" )
      edge( id → cid )
      id

    case _:Break ⇒
      node( "break" )

    case _:Continue ⇒
      node( "continue" )

    case Range(n1, n2) ⇒
      if (n1 == n2) node( n1.toString )
      else node( "[" + n1 + ", " + n2 + "]" )

    case Var(x) ⇒
      node( x )

    case Binop(op, e1, e2) ⇒
      val cid1 = dotify(e1)
      val cid2 = dotify(e2)
      val id = node( op.toString )
      edge( id → cid1 )
      edge( id → cid2 )
      id

    case Strs(strs) ⇒
      if (strs.size == 1) node( strs.head )
      else node( "[" + strs.mkString(",") + "]" )
  }

}
