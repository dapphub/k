// Copyright (c) 2016-2018 K Team. All Rights Reserved.

package org.kframework.definition

import org.junit.{Assert, Test}
import org.kframework.kore.KORE.Att
import org.kframework.kore.KORE.Sort

class OuterTest {
  @Test def isPrefixTest: Unit = {
    val sort = Sort("foo")
    val nt = NonTerminal(sort, None)
    val prod1 = Production(sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(")")), Att)
    Assert.assertTrue(prod1.isPrefixProduction)
    val prod2 = Production(sort, Seq(Terminal("foo")), Att)
    Assert.assertFalse(prod2.isPrefixProduction)
    val prod3 = Production(sort, Seq(Terminal("foo"), Terminal("(")), Att)
    Assert.assertFalse(prod3.isPrefixProduction)
    val prod4 = Production(sort, Seq(Terminal("foo"), Terminal("("), nt), Att)
    Assert.assertFalse(prod4.isPrefixProduction)
    val prod5 = Production(sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(",")), Att)
    Assert.assertFalse(prod5.isPrefixProduction)
    val prod6 = Production(sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(","), nt), Att)
    Assert.assertFalse(prod6.isPrefixProduction)
    val prod7 = Production(sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(","), Terminal(")")), Att)
    Assert.assertFalse(prod7.isPrefixProduction)
    val prod8 = Production(sort, Seq(Terminal("foo"), Terminal("("), Terminal(")")), Att)
    Assert.assertTrue(prod8.isPrefixProduction)
    val prod9 = Production(sort, Seq(Terminal("("), Terminal(")")), Att)
    Assert.assertTrue(prod9.isPrefixProduction)
    val prod10 = Production(sort, Seq(Terminal("("), nt, Terminal(","), nt, Terminal(")")), Att)
    Assert.assertTrue(prod10.isPrefixProduction)
  }

  @Test def recordProductions: Unit = {
    val sort1 = Sort("foo1")
    val sort2 = Sort("foo2")
    val nt1 = NonTerminal(sort1, Some("bar"))
    val nt2 = NonTerminal(sort2, Some("baz"))
    val prod = Production(sort1, Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")), Att)
    val newAtt = Att.add("recordPrd", classOf[Production], prod).add("unparseAvoid")
    val records = prod.recordProductions
    Assert.assertEquals(4, records.size)
    Assert.assertEquals(Set(
      Production(sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal(")")), newAtt),
      Production(sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal("baz"), Terminal(":"), nt2, Terminal(")")), newAtt),
      Production(sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal("bar"), Terminal(":"), nt1, Terminal(")")), newAtt),
      Production(sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal("bar"), Terminal(":"), nt1, Terminal(","), Terminal("baz"), Terminal(":"), nt2,Terminal(")")), newAtt)
    ), records)
  }
}
