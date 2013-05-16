package neilessy.alg.btree3

import annotation.tailrec

object BTree {
  val maxNode = 4
  val halfNode = maxNode / 2

  def zipHeadWithTail[T]( list: List[T]) = zipHeadWithTail0( list, Nil )

  @tailrec
  private def zipHeadWithTail0[T]( list: List[T], acc: List[(T,List[T])] ): List[(T,List[T])] = {
    val head::tail = list
    if ( tail.isEmpty ) ((head,tail)::acc).reverse
    else zipHeadWithTail0( tail, (head,tail)::acc )
  }
  private class genericCompare[K <: Comparable[K]] extends ((K, K) => Int) {
    def apply(x:K,y:K) = x.compareTo(y)
  }
  private val _comparableEmpty: BTree[Nothing, Nothing] =
    new BTree[Nothing,Nothing]( new genericCompare, null,Nil)
  private val _boolEmpty: BTree[Boolean, Nothing] =
    new BTree( (a:Boolean,b:Boolean) => if ( ( a && b ) || (!a && !b) ) 0 else if ( a ) 1 else -1 , null, Nil)
  private val _byteEmpty: BTree[Byte, Nothing] =
    new BTree( (a:Byte,b:Byte) => a - b, null, Nil)
  private val _charEmpty: BTree[Char, Nothing] =
    new BTree( (a:Char,b:Char) => a - b, null, Nil)
  private val _shortEmpty: BTree[Short, Nothing] =
    new BTree( (a:Short,b:Short) => a - b, null, Nil)
  private val _intEmpty: BTree[Int, Nothing] =
    new BTree( (a:Int,b:Int) => a - b, null, Nil)
  private val _longEmpty: BTree[Long, Nothing] =
    new BTree( (a:Long,b:Long) => if ( a == b ) 0 else if ( a > b ) 1 else -1, null, Nil)
  private val _floatEmpty: BTree[Float, Nothing] =
    new BTree( (a:Float,b:Float) => if ( a == b ) 0 else if ( a > b ) 1 else -1, null, Nil)
  private val _doubleEmpty: BTree[Double, Nothing] =
    new BTree( (a:Double,b:Double) => if ( a == b ) 0 else if ( a > b ) 1 else -1, null, Nil)

  def empty[K,V]( compare: (K,K) => Int ) = new BTree[K,V]( compare, null, Nil )
  def empty[K <: Comparable[K],V]() = _comparableEmpty.asInstanceOf[BTree[K,V]]
  def emptyBool[K <: Boolean,V]() = _boolEmpty.asInstanceOf[BTree[K,V]]
  def emptyByte[K <: Byte,V]() = _byteEmpty.asInstanceOf[BTree[K,V]]
  def emptyChar[K <: Char,V]() = _charEmpty.asInstanceOf[BTree[K,V]]
  def emptyShort[K <: Short,V]() = _shortEmpty.asInstanceOf[BTree[K,V]]
  def emptyInt[K <: Int,V]() = _intEmpty.asInstanceOf[BTree[K,V]]
  def emptyLong[K <: Long,V]() = _longEmpty.asInstanceOf[BTree[K,V]]
  def emptyFloat[K <: Float,V]() = _floatEmpty.asInstanceOf[BTree[K,V]]
  def emptyDouble[K <: Double,V]() = _doubleEmpty.asInstanceOf[BTree[K,V]]
}

case class BTree[K,V]( compare: (K,K) => Int, before: BTree[K,V], entries: List[(K,V,BTree[K,V])] ) {
  import BTree._
  def isEmpty = isLeaf && nodeSize == 0
  def size = size0( nodeSize, List(getChildNodes) )
  def empty = new BTree[K,V]( compare, null, Nil )
  def contains( key: K ) = contains0( key, this )
  def get( key: K ) = get0( key, this )
  def update( key: K, value: V ) = update0( key, value, this, Nil )
  def insert( key: K, value: V ) = insert0( key, value, this, Nil )
  def remove( key: K ) = remove0( key, this, Nil )
  def put( key: K, value: V ) = put0( key, value, this, Nil )
  def isLeaf = before eq null

  def newLeaf( entries: List[(K,V,BTree[K,V])] ): BTree[K,V] = new BTree[K,V]( compare, null, entries )
  def newBranch( before: BTree[K,V], entries: List[(K,V,BTree[K,V])] ): BTree[K,V] = new BTree[K,V]( compare, before, entries )
  
  private def isFull = nodeSize == maxNode
  private def isTooSmall = nodeSize < halfNode
  private def isTooBig = nodeSize > maxNode

  @tailrec
  private def size0( acc: Int, stack: List[List[BTree[K,V]]]): Int =
    if ( stack.isEmpty ) acc
    else {
      val level::tail = stack
      val node::rest = level
      val children = node.getChildNodes
      val newAcc = acc + node.nodeSize
      if ( children.isEmpty )
        if ( rest.isEmpty ) size0( newAcc, tail )
        else size0( newAcc, rest :: tail )
      else if ( rest.isEmpty ) size0( newAcc, children :: tail )
      else size0( newAcc, children :: rest :: tail )
    }

  @tailrec
  private def contains0( key: K, node: BTree[K,V] ): Boolean =
      if ( node.isLeaf ) node owns key
      else {
        val branch = node
        if ( branch isAfter key )
          contains0( key, branch.before )
        else if ( branch owns key ) true
        else contains0( key, branch childFor key )
      }

  @tailrec
  private def get0( key: K, node: BTree[K,V] ): Option[V] =
    if ( node.isLeaf ) node getHere key
    else {
      if ( node isAfter key )
        get0( key, node.before )
      else node getHere key match {
        case v: Some[V] => v
        case None => get0( key, node childFor key )
      }
    }

  @tailrec
  private def updateHistory( o: BTree[K,V], n: BTree[K,V], history: List[BTree[K,V]] ): BTree[K,V] =
    if ( history.isEmpty ) n else updateHistory( history.head, history.head.updateNode(o,n), history.tail )

  @tailrec
  private def originalRoot( node: BTree[K,V], history: List[BTree[K,V]] ): BTree[K,V] =
    if ( history.isEmpty ) node else originalRoot( history.head, history.tail )

  @tailrec
  private def update0( key: K, value: V, node: BTree[K,V], history: List[BTree[K,V]] ): BTree[K,V] =
    if ( node.isLeaf ) {
      if ( node owns key ) updateHistory( node, node.updateHere( key, value ), history )
      else originalRoot( node, history )
    } else {
      if ( node isAfter key )
        update0( key, value, node.before, node :: history )
      else if ( node owns key )
        updateHistory( node, node.updateHere( key, value ), history )
      else
        update0( key, value, node childFor key, node :: history )
    }

  @tailrec
  private def insert0( key: K, value: V, node: BTree[K,V], history: List[BTree[K,V]] ): BTree[K,V] =
    if ( node.isLeaf ) {
      if ( node owns key ) originalRoot( node, history )
      else if ( !node.isFull ) updateHistory( node, node.insertHere( (key,value,null) ), history )
      else {
        val (left,upEntry) = node.insertAndSplit((key,value,null))
        if ( history.isEmpty ) 
          newBranch(left,upEntry::Nil)
        else
          insertSplit( node, left, upEntry, history )
      }
    } else {
      if ( node isAfter key )
        insert0( key, value, node.before, node :: history )
      else if ( node owns key )
        originalRoot( node, history )
      else 
        insert0( key, value, node childFor key, node :: history )
    }

  @tailrec
  private def put0( key: K, value: V, node: BTree[K,V], history: List[BTree[K,V]] ): BTree[K,V] =
    if ( node.isLeaf ) {
      if ( node owns key ) updateHistory( node, node.updateHere( key, value ), history )
      else if ( !node.isFull ) updateHistory( node, node.insertHere( (key,value,null) ), history )
      else {
        val (left,upEntry) = node.insertAndSplit((key,value,null))
        if ( history.isEmpty ) 
          newBranch(left,upEntry::Nil)
        else
          insertSplit( node, left, upEntry, history )
      }
    } else {
      if ( node isAfter key )
        put0( key, value, node.before, node :: history )
      else if ( node owns key )
        updateHistory( node, node.updateHere( key, value ), history )
      else 
        put0( key, value, node childFor key, node :: history )
    }

  private def insertAndSplit( entry: (K,V,BTree[K,V]) ): (BTree[K,V],(K,V,BTree[K,V])) = {
    val (left,splitter::right) = insertEntry( entry, entries, Nil ).splitAt(halfNode)
    (newLeaf(left),(splitter._1,splitter._2,newLeaf(right)))
  }

  @tailrec
  private def insertSplit( o: BTree[K,V], n: BTree[K,V], entry: (K,V,BTree[K,V]), history: List[BTree[K,V]] ): BTree[K,V] = {
    if ( history.isEmpty ) newBranch(n,entry::Nil)
    else {
      val node::moreHistory = history
      if ( node.isFull ) {
        val (left,upEntry) = node.updateInsertAndSplit(o,n,entry)
        insertSplit( node, left, upEntry, moreHistory )
      } else node.updateAndInsert(o,n,entry)
    }
  }

  private def parentIsSingle( merged: BTree[K,V], parentHistory: List[BTree[K,V]] ) = 
    if ( ! parentHistory.isEmpty ) throw new RuntimeException("!")
    else if ( merged.isTooBig ) {
      val (newLeft,upEntry) = merged.split()
      newBranch( newLeft, upEntry :: Nil )
    }
    else merged

  private def mergedIsTooBig( key: K, left: BTree[K,V], merged: BTree[K,V], branch: BTree[K,V], history: List[BTree[K,V]] ) = {
    val (newLeft,upEntry) = merged.split()
    val newBranch = branch.removeHere(key,left,newLeft).insertHere(upEntry)
    updateHistory( branch, newBranch, history )
  }

  @tailrec
  private def remove0( key: K, node: BTree[K,V], history: List[BTree[K,V]] ): BTree[K,V] = {
    if ( node.isLeaf ) {
      val leaf = node
      if ( !(leaf owns key) ) originalRoot( node, history )
      else {
        val newLeaf2 = leaf.removeHere(key)
        if ( history.isEmpty ) newLeaf2 
        else if ( ! newLeaf2.isTooSmall ) updateHistory( leaf, newLeaf2, history )
        else {
          val parent::parentHistory = history
          val (leafKey, left, merged ) =
            if ( parent.before eq leaf ) {
              val leafKey = parent.firstKey
              val leafValue = parent.getHere(leafKey).get
              val right = parent.childFor(leafKey)
              ( leafKey, leaf, newLeaf( newLeaf2.entries ::: (leafKey,leafValue,null) :: right.entries ) )
            } else {
              val (leafKey,leafValue,_) = parent.entryForChild(leaf)
              val (left,_) = parent.getLeftRight(leafKey)
              ( leafKey, left, newLeaf( left.entries ::: (leafKey,leafValue,null) :: newLeaf2.entries ) )
            }
          if ( parent.isSingle ) parentIsSingle( merged, parentHistory )
          else if ( merged.isTooBig ) mergedIsTooBig( leafKey, left, merged, parent, parentHistory )
          else pullDown( parent, parent.removeHere( leafKey, left, merged ), parentHistory )
        }
      }
    } else {
      val branch = node
      if ( branch isAfter key )
        remove0( key, branch.before, branch :: history )
      else if ( branch owns key ) {
        val (left,right) = branch.getLeftRight(key)
        val merged = {
          if ( left.isLeaf )
            if ( right.isLeaf ) newLeaf(left.entries ::: right.entries)
            else throw new RuntimeException("!")
          else
            if ( !right.isLeaf ) merge( left, right )
            else throw new RuntimeException("!")
        }
        if ( merged.isTooBig ) mergedIsTooBig( key, left, merged, branch, history ) 
        else pullDown( branch, branch.removeHere(key,left,merged), history )
      }
      else remove0( key, branch childFor key, branch :: history )
    }
  }

  private def merge( left: BTree[K,V], right: BTree[K,V] ): BTree[K,V] = mergeDown( left, right, Nil )
  
  @tailrec
  private def mergeDown( left: BTree[K,V], right: BTree[K,V], stack: List[(BTree[K,V],BTree[K,V])] ): BTree[K,V] = {
    val l = left.lastChild
    val r = right.before
    if ( l.isLeaf )
      if ( r.isLeaf ) mergeUp( left, right, stack, newLeaf( l.entries ::: r.entries ) )
      else throw new RuntimeException("!")
    else
      if ( !r.isLeaf ) mergeDown( l, r, ((left,right))::stack )
      else throw new RuntimeException("!")
  }

  @tailrec
  private def mergeUp( left: BTree[K,V], right: BTree[K,V], stack: List[(BTree[K,V],BTree[K,V])], middleChild: BTree[K,V] ): BTree[K,V] = {
    val combine =
      if ( middleChild.isTooBig ) {
        val (newMiddleChild,upEntry) = middleChild.split()
        newBranch( left.before, left.updateChild(left.lastChild,newMiddleChild,left.entries,Nil) ::: upEntry :: right.entries )
      } else newBranch( left.before, left.updateChild(left.lastChild,middleChild,left.entries,Nil) ::: right.entries )
    if ( stack.isEmpty ) combine
    else mergeUp( stack.head._1, stack.head._2, stack.tail, combine )
  }

  @tailrec
  private def pullDown( o: BTree[K,V], n: BTree[K,V], history: List[BTree[K,V]] ): BTree[K,V] =
    if ( ! n.isTooSmall ) updateHistory(o,n,history)
    else if ( history.isEmpty ) n
    else {
      val parent::parentHistory = history
      val (key,left,merged) =
        if ( parent.before eq o ) {
          val key = parent.firstKey
          val child = parent.childFor(key)
          val value = parent.getHere(key).get
          ( key, o, newBranch( n.before, n.entries ::: (key,value,child.before) :: child.entries ) )
        } else {
          val (key,value,_) = parent.entryForChild( o )
          val (left,_) = parent.getLeftRight( key )
          ( key, left, newBranch( left.before, left.entries ::: (key,value,n.before) :: n.entries ) )
        }
      if ( parent.isSingle ) parentIsSingle( merged, parentHistory )
      else if ( merged.isTooBig ) mergedIsTooBig( key, left, merged, parent, parentHistory ) 
      else pullDown( parent, parent.removeHere(key,left,merged), history )
    }
  private def nodeSize = entries.size
  private def getChildNodes = before :: ( entries map { _._3 } )
  private def split() = {
    val (left,splitter::right) = entries.splitAt(entries.size/2)
    (newBranch(before,left),(splitter._1,splitter._2,newBranch(splitter._3,right)))
  }
  private def firstKey = entries.head._1
  private def isSingle = entries.size == 1
  private def isAfter( key: K ) = compare( firstKey, key ) > 0
  private def entryForChild( node: BTree[K,V] ) = (entries find { _._3 eq node }).get
  private def childFor( key: K ) =
    (zipHeadWithTail(entries) find { e =>
      val (_, tail) = e
      (tail.isEmpty || compare( tail.head._1, key ) > 0)
    }).get._1._3
  private def lastChild = entries.last._3
  @tailrec private final def updateChild( o: BTree[K,V], n: BTree[K,V], entries: List[(K,V,BTree[K,V])], prior: List[(K,V,BTree[K,V])] ): List[(K,V,BTree[K,V])] =
    if ( entries.isEmpty )
      throw new RuntimeException("!")
    else {
      val head::tail = entries
      if ( head._3 eq o )
        prior reverse_::: head.copy( _3 = n ) :: tail
      else updateChild( o, n, tail, head :: prior )
    }
  private def updateNode( o: BTree[K,V], n: BTree[K,V] ) =
    if ( before eq o ) newBranch( n, entries)
    else newBranch( before, updateChild( o, n, entries, Nil ) ) 

  @tailrec
  private def updateEntry( key: K, value: V, entries: List[(K,V,BTree[K,V])], prior: List[(K,V,BTree[K,V])] ): List[(K,V,BTree[K,V])] =
    if ( entries.isEmpty )
      throw new RuntimeException("!")
    else {
      val head::tail = entries
      if ( compare( head._1, key ) == 0 ) prior reverse_::: head.copy( _2 = value ) :: tail
      else updateEntry( key, value, tail, head :: prior )
    }

  @tailrec
  private def insertEntry( entry: (K,V,BTree[K,V]), entries: List[(K,V,BTree[K,V])], prior: List[(K,V,BTree[K,V])] ): List[(K,V,BTree[K,V])] =
    if ( entries.isEmpty ) prior reverse_::: entry :: Nil
    else {
      val head::tail = entries
      if ( compare( head._1, entry._1 ) > 0 ) prior reverse_::: entry :: entries
      else insertEntry( entry, tail, head :: prior )
    }
  
  @tailrec
  private def removeEntry( key: K, entries: List[(K,V,BTree[K,V])], prior: List[(K,V,BTree[K,V])] ) : List[(K,V,BTree[K,V])] =
    if ( entries.isEmpty ) prior.reverse
    else {
      val head::tail = entries
      if ( compare( head._1, key ) == 0 ) prior reverse_::: tail
      else removeEntry( key, tail, head :: prior )
    }
  
  private def getLeftRight( key: K ): (BTree[K,V],BTree[K,V]) = getLeftRight( key, before, entries )

  @tailrec
  private def getLeftRight( key: K, left: BTree[K,V], entries: List[(K,V,BTree[K,V])] ): (BTree[K,V],BTree[K,V]) =
    if ( entries.isEmpty ) throw new RuntimeException("!")
    else {
      val head::tail = entries
      if ( compare( head._1, key ) == 0 ) ((left,head._3))
      else getLeftRight( key, head._3, tail )
    }

  private def owns( key: K ) = !(entries forall { e => compare( e._1, key ) != 0 })
  private def getHere( key: K ) = entries find { e => compare( e._1, key ) == 0 } map { _._2 }
  private def updateHere( key: K, value: V ) = newBranch( before, updateEntry( key, value, entries, Nil ) )
  private def insertHere( entry: (K,V,BTree[K,V]) ) = newBranch( before, insertEntry( entry, entries, Nil ) )
  private def updateAndInsert( o: BTree[K,V], n: BTree[K,V], entry: (K,V,BTree[K,V]) ) = {
    val uBefore = if ( before eq o ) n else before
    val uEntries = if ( before eq o ) entries else updateChild( o, n, entries, Nil ) 
    newBranch(uBefore,insertEntry( entry, uEntries, Nil ))
  }
  private def updateInsertAndSplit( o: BTree[K,V], n: BTree[K,V], entry: (K,V,BTree[K,V]) ) = {
    val uBefore = if ( before eq o ) n else before
    val uEntries = if ( before eq o ) entries else updateChild( o, n, entries, Nil ) 
    val (left,splitter::right) = insertEntry( entry, uEntries, Nil ).splitAt(halfNode)
    (newBranch(uBefore,left),(splitter._1,splitter._2,newBranch(splitter._3,right)))
  }
  private def removeHere( key: K ) = newLeaf( removeEntry( key, entries, Nil ) )
  private def removeHere( key: K, o: BTree[K,V], n: BTree[K,V] ) =
    if ( compare( firstKey, key ) == 0 )
      newBranch( n, removeEntry( key, entries, Nil ) )
    else
      newBranch( before, removeEntry( key, updateChild( o, n, entries, Nil ), Nil ) )
}