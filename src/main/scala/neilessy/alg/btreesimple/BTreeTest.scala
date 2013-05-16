package neilessy.alg.btreesimple

import annotation.tailrec

object BTreeTest {
  import BTree._
  def main( args: Array[String] ) {
    zipHeadWithTailTest()
    tests()
    mainTest()
    synchronized { wait( 500 ) }
  }
  def zipHeadWithTailTest() {
    println("### test - zipHeadWithTail")
    println(zipHeadWithTail(List(1,2,3)))
  }
  val testTree: Branch[String,String] =
    Branch[String,String](
      Leaf(List(("a","-"),("b","-"))),
      List(
        ("c","-",Leaf(List(("d","-"),("e","-"))))
        ,("f","-",Leaf(List(("g","-"),("h","-"))))
      )
    )
  val testTree2: Branch[String,String] =
    Branch[String,String](
      Leaf(List(("i","-"),("j","-"))),
      List(
        ("k","-",Leaf(List(("l","-"),("m","-"))))
        ,("n","-",Leaf(List(("o","-"),("p","-"))))
      )
    )
  def tests() {
    println( "### test - tree " )
    println( "testTree = " + testTree )
    println( "testTree childFor e: " + ( testTree childFor "e" ) )
    println( "testTree isAfter c: " + ( testTree isAfter "c" ) )
    println( "testTree owns z: " + ( testTree owns "z" ) )
    println( "testTree getHere z: " + ( testTree getHere "z" ) )
  }
  def countChars( str: String, ch: Char ) = str.foldLeft(0) { (b,c) => if ( c == ch ) b+1 else b }
  def prettyPrint( str: Object ) { prettyPrint( str.toString.replace(", ",","), 0, wasNewLine = false ) }
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
    val bTree = BTree.empty[String,Int]
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
  }
}