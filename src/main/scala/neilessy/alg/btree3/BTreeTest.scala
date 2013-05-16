package neilessy.alg.btree3

import annotation.tailrec


object BTreeTest {
  import BTree._
  def main( args: Array[String] ) {
    zipHeadWithTailTest()
    tests()
    mainTest()
    secondTest()
    thirdTest()
    synchronized { wait( 500 ) }
  }
  def zipHeadWithTailTest() {
    println("### test - zipHeadWithTail")
    println(zipHeadWithTail(List(1,2,3)))
  }
  val testTree: BTree[String,String] = BTree.empty()
    .insert("a","-")
    .insert("b","-")
    .insert("c","-")
    .insert("d","-")
    .insert("e","-")
    .insert("f","-")
    .insert("g","-")
    .insert("h","-")
  val testTree2: BTree[String,String] = BTree.empty()
    .insert("i","-")
    .insert("j","-")
    .insert("k","-")
    .insert("l","-")
    .insert("m","-")
    .insert("n","-")
    .insert("o","-")
    .insert("p","-")
  def tests() {
    println( "### test - tree " )
    println( "testTree = " + testTree )
  }
  def countChars( str: String, ch: Char ) = str.foldLeft(0) { (b,c) => if ( c == ch ) b+1 else b }
  def prettyPrint( str: Object ) { prettyPrint(
    str.toString
      .replace(", ",",")
      .replace("null,","")
      .replace(",null)",")")
      .replace("<function2>,","")
    , 0, wasNewLine = false ) }
  @tailrec def prettyPrint( str: String, level: Int, wasNewLine: Boolean ) {
    if ( wasNewLine )
      1 to level foreach { i => print(" ") }
    val indexOpen = str.indexOf('(')
    val indexClose = str.indexOf(')') 
    if ( indexOpen > -1 && ( indexOpen < indexClose || indexClose == -1 ) ) {
      val indexOpen2 = str.indexOf('(',indexOpen+1)
      val indexComma = str.indexOf(',',indexClose+1)
      val ( ( thisLine, nextLine ), newLevel, newLine ) =
        if ( indexClose > -1 && indexClose < indexOpen2 && indexComma > indexClose && indexComma < indexOpen2 )
          ( str.splitAt( indexComma + 1 ), level - countChars( str.substring( indexClose + 1, indexComma ), ')' ), true )
        else if ( indexClose > -1 && indexClose < indexOpen2 ) ( str.splitAt( indexOpen2 ), level - countChars( str.substring( indexClose + 1, indexOpen2 ), ')' ), true )
        else if ( indexOpen == 0 ) ( str.splitAt( indexOpen + 1 ), level + 1, false )
        else ( str.splitAt( indexOpen + 1 ), level + 1, true )
      if ( newLine ) println( thisLine ) else print( thisLine )
      prettyPrint( nextLine, newLevel, newLine )
    } else if ( indexClose > -1 && ( indexClose < indexOpen || indexOpen == -1 ) ) {
      val indexClose2 = str.indexOf(')',indexClose+1)
      val ( ( thisLine, nextLine ), newLevel, newLine ) =
        if ( indexClose == 0 && indexOpen > -1 && ( indexClose2 == -1 || indexClose2 > indexOpen ) ) ( str.splitAt( indexOpen ), level, true )
        else if ( indexClose == 0 && indexOpen > -1 && ( indexClose2 == -1 || indexClose2 < indexOpen ) ) ( str.splitAt( indexOpen + 1 ), level - 1, true )
        else if ( indexOpen == -1 ) ( str.splitAt( indexClose + 1 ), level - 1, false )
        else if ( indexClose == 0 ) ( str.splitAt( 1 ), level - 1, true )
        else ( str.splitAt( indexClose ), level, true )
      if ( newLine ) println( thisLine ) else print( thisLine )
      prettyPrint( nextLine, newLevel, newLine )
    } else println( str )
  }
  def mainTest() {
    println("### test - main")
    var bTree = BTree.empty[String,Int]()
      .insert("hello",1)
      .insert("bye",2)
      .insert("chow",3)
      .insert("mary",4)
      .insert("bob",5)
      .insert("henry",6)
      .insert("manny",7)
      .insert("margret",8)
      .insert("valentino",9)
    println( " original    => "); prettyPrint( bTree )
    bTree = bTree.remove("manny")
    println( " - manny     => "); prettyPrint( bTree )
    bTree = bTree.remove("bye")
    println( " - bye       => "); prettyPrint( bTree )
    bTree = bTree.remove("bob")
    println( " - bob       => "); prettyPrint( bTree )
    bTree = bTree.remove("valentino")
    println( " - valentino => "); prettyPrint( bTree )
    bTree = bTree.remove("chow")
    println( " - chow      => "); prettyPrint( bTree )
  }
  def secondTest() {
    println("### test - main")
    var bTree = BTree.emptyInt[Int,String]()
      .insert(1,"hello")
      .insert(2,"bye")
      .insert(3,"chow")
      .insert(4,"mary")
      .insert(5,"bob")
      .insert(6,"henry")
      .insert(7,"manny")
      .insert(8,"margret")
      .insert(9,"valentino")
    println( " original    => "); prettyPrint( bTree )
    bTree = bTree.remove(7)
    println( " - manny     => "); prettyPrint( bTree )
    bTree = bTree.remove(2)
    println( " - bye       => "); prettyPrint( bTree )
    bTree = bTree.remove(5)
    println( " - bob       => "); prettyPrint( bTree )
    bTree = bTree.remove(9)
    println( " - valentino => "); prettyPrint( bTree )
    bTree = bTree.remove(3)
    println( " - chow      => "); prettyPrint( bTree )
  }
  class RichInt( val i: Int ) extends AnyVal with Ordered[RichInt] {
    def compare(that: RichInt) = that.i - i // reverse the ordering
    override def toString = i.toString
  }
  implicit def toRichInt( i: Int ) = new RichInt( i ) 
  def thirdTest() {
    println("### test - main")
    var bTree = BTree.empty[RichInt,String]()
      .insert(1,"hello")
      .insert(2,"bye")
      .insert(3,"chow")
      .insert(4,"mary")
      .insert(5,"bob")
      .insert(6,"henry")
      .insert(7,"manny")
      .insert(8,"margret")
      .insert(9,"valentino")
    println( " original    => "); prettyPrint( bTree )
    bTree = bTree.remove(7)
    println( " - manny     => "); prettyPrint( bTree )
    bTree = bTree.remove(2)
    println( " - bye       => "); prettyPrint( bTree )
    bTree = bTree.remove(5)
    println( " - bob       => "); prettyPrint( bTree )
    bTree = bTree.remove(9)
    println( " - valentino => "); prettyPrint( bTree )
    bTree = bTree.remove(3)
    println( " - chow      => "); prettyPrint( bTree )
  }
}