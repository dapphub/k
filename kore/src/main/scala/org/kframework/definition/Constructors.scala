// Copyright (c) 2014-2018 K Team. All Rights Reserved.

package org.kframework.definition

import java.util.Optional

import org.kframework.attributes.Att
import org.kframework.{attributes, definition}
import org.kframework.kore._
import collection._

/**
 *
 * Helper constructors for KORE definition.classes. The class is meant to be imported
 * statically.
 *
 */

object Constructors {

  def Definition(mainModule: Module, modules: Set[Module], att: Att) =
    definition.Definition(mainModule, modules, att)

  def Module(name: String, imports: Set[Module], sentences: Set[Sentence], att: attributes.Att) =
    definition.Module(name, imports, sentences, att)

  def SyntaxSort(sort: Sort) = definition.SyntaxSort(sort)
  def SyntaxSort(sort: Sort, att: attributes.Att) = definition.SyntaxSort(sort, att)

  def Production(sort: Sort, items: Seq[ProductionItem]) = definition.Production(sort, items, Att.empty)
  def Production(sort: Sort, items: Seq[ProductionItem], att: attributes.Att) = definition.Production(sort, items, att)
  def Production(klabel: KLabel, sort: Sort, items: Seq[ProductionItem]) = definition.Production(klabel, sort, items)
  def Production(klabel: KLabel, sort: Sort, items: Seq[ProductionItem], att: attributes.Att) = definition.Production(klabel, sort, items, att)

  def Terminal(s: String) = definition.Terminal(s)
  def NonTerminal(sort: Sort) = definition.NonTerminal(sort, None)
  def NonTerminal(sort: Sort, name: Option[String]) = definition.NonTerminal(sort, name)
  def RegexTerminal(regexString: String) = definition.RegexTerminal("#", regexString, "#")
  def RegexTerminal(precedeRegexString: String, regexString: String, followRegexString: String) = definition.RegexTerminal(precedeRegexString, regexString, followRegexString)

  def Tag(s: String) = definition.Tag(s)

  def SyntaxPriority(priorities: Seq[Set[Tag]]) = definition.SyntaxPriority(priorities)
  def SyntaxPriority(priorities: Seq[Set[Tag]], att: attributes.Att) = definition.SyntaxPriority(priorities, att)

  def SyntaxAssociativity(assoc: definition.Associativity.Value, tags: Set[Tag]) = definition.SyntaxAssociativity(assoc, tags)
  def SyntaxAssociativity(assoc: definition.Associativity.Value, tags: Set[Tag], att: attributes.Att) = definition.SyntaxAssociativity(assoc, tags, att)

  def Context(content: K, requires: K) = definition.Context(content, requires)
  def Context(content: K, requires: K, att: attributes.Att) = definition.Context(content, requires, att)

  def Rule(body: K, requires: K, ensures: K, att: attributes.Att) = definition.Rule(body, requires, ensures, att)
  def Rule(body: K, requires: K, ensures: K) = definition.Rule(body, requires, ensures, Att.empty)

  def Bubble(sentenceType: String, content: String, att: attributes.Att) =
    definition.Bubble(sentenceType, content, att)

  def Associativity = definition.Associativity;

  // EXTRA

  def Configuration(body: K, ensures: K, att: attributes.Att) = definition.Configuration(body, ensures, att)
}
