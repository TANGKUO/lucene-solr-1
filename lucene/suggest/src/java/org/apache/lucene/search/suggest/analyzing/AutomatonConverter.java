package org.apache.lucene.search.suggest.analyzing;

/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import org.apache.lucene.analysis.Analyzer;
import org.apache.lucene.analysis.TokenStream;
import org.apache.lucene.analysis.TokenStreamToAutomaton;
import org.apache.lucene.util.BytesRef;
import org.apache.lucene.util.IntsRef;
import org.apache.lucene.util.automaton.Automaton;
import org.apache.lucene.util.automaton.BasicAutomata;
import org.apache.lucene.util.automaton.BasicOperations;
import org.apache.lucene.util.automaton.LevenshteinAutomata;
import org.apache.lucene.util.automaton.SpecialOperations;
import org.apache.lucene.util.automaton.State;
import org.apache.lucene.util.automaton.Transition;
import org.apache.lucene.util.automaton.UTF32ToUTF8;
import org.apache.lucene.util.fst.FST;

public class AutomatonConverter {
  
  protected final boolean unicodeAware;
  
  public static final AutomatonConverter DEFAULT_CONVERTER = new AutomatonConverter(false);
  
  /** Represents the separation between tokens, if
   *  PRESERVE_SEP was specified */
  private static final int SEP_LABEL = '\u001F';
  
  public AutomatonConverter(boolean unicodeAware) {
    this.unicodeAware = unicodeAware;
  }

  public <T> List<FSTUtil.Path<T>> getFullPrefixPaths(
      List<FSTUtil.Path<T>> prefixPaths, Automaton lookupAutomaton, FST<T> fst) throws IOException {
    return prefixPaths;
  }
  
  public Automaton convertAutomaton(Automaton a) {
    return a;
  }
  
  public TokenStreamToAutomaton newTokenStreamToAutomaton(
      boolean preservePositionIncrements) {
    final TokenStreamToAutomaton tsta = new TokenStreamToAutomaton();
    tsta.setPreservePositionIncrements(preservePositionIncrements);
    tsta.setUnicodeArcs(unicodeAware);
    return tsta;
  }
  
  public final Set<IntsRef> toFiniteStrings(final BytesRef surfaceForm, final TokenStreamToAutomaton ts2a, Analyzer analyzer, final int maxGraphExpansions, final boolean preserveSep) throws IOException {
    // Analyze surface form:
       TokenStream ts = analyzer.tokenStream("", surfaceForm.utf8ToString());

       // Create corresponding automaton: labels are bytes
       // from each analyzed token, with byte 0 used as
       // separator between tokens:
       Automaton automaton = ts2a.toAutomaton(ts);
       ts.close();

       replaceSep(automaton, preserveSep);
       automaton = convertAutomaton(automaton);

       assert SpecialOperations.isFinite(automaton);

       // Get all paths from the automaton (there can be
       // more than one path, eg if the analyzer created a
       // graph using SynFilter or WDF):

       // TODO: we could walk & add simultaneously, so we
       // don't have to alloc [possibly biggish]
       // intermediate HashSet in RAM:
       return SpecialOperations.getFiniteStrings(automaton, maxGraphExpansions);
     }

     public final Automaton toLookupAutomaton(final CharSequence key, Analyzer analyzer, TokenStreamToAutomaton t2a, boolean preserveSep) throws IOException {
       // TODO: is there a Reader from a CharSequence?
       // Turn tokenstream into automaton:
       TokenStream ts = analyzer.tokenStream("", key.toString());
       Automaton automaton = t2a.toAutomaton(ts);
       ts.close();

       // TODO: we could use the end offset to "guess"
       // whether the final token was a partial token; this
       // would only be a heuristic ... but maybe an OK one.
       // This way we could eg differentiate "net" from "net ",
       // which we can't today...

       replaceSep(automaton, preserveSep);

       // TODO: we can optimize this somewhat by determinizing
       // while we convert
       BasicOperations.determinize(automaton);
       return automaton;
     }
  
   // Replaces SEP with epsilon or remaps them if
   // we were asked to preserve them:
   private void replaceSep(Automaton a, boolean preserveSeparators) {

     State[] states = a.getNumberedStates();

     // Go in reverse topo sort so we know we only have to
     // make one pass:
     for(int stateNumber=states.length-1;stateNumber >=0;stateNumber--) {
       final State state = states[stateNumber];
       List<Transition> newTransitions = new ArrayList<Transition>();
       for(Transition t : state.getTransitions()) {
         assert t.getMin() == t.getMax();
         if (t.getMin() == TokenStreamToAutomaton.POS_SEP) {
           if (preserveSeparators) {
             // Remap to SEP_LABEL:
             newTransitions.add(new Transition(SEP_LABEL, t.getDest()));
           } else {
             copyDestTransitions(state, t.getDest(), newTransitions);
             a.setDeterministic(false);
           }
         } else if (t.getMin() == TokenStreamToAutomaton.HOLE) {

           // Just remove the hole: there will then be two
           // SEP tokens next to each other, which will only
           // match another hole at search time.  Note that
           // it will also match an empty-string token ... if
           // that's somehow a problem we can always map HOLE
           // to a dedicated byte (and escape it in the
           // input).
           copyDestTransitions(state, t.getDest(), newTransitions);
           a.setDeterministic(false);
         } else {
           newTransitions.add(t);
         }
       }
       state.setTransitions(newTransitions.toArray(new Transition[newTransitions.size()]));
     }
   }
  
  private void copyDestTransitions(State from, State to,
      List<Transition> transitions) {
    if (to.isAccept()) {
      from.setAccept(true);
    }
    for (Transition t : to.getTransitions()) {
      transitions.add(t);
    }
  }
  
  public static class FuzzyAutomatonConverter extends AutomatonConverter {
    private final int maxEdits;
    private final boolean transpositions;
    private final int nonFuzzyPrefix;
    private final int minFuzzyLength;

    /**
     * Creates a {@link FuzzyAutomatonConverter} instance.
     * 
     * @param maxEdits must be >= 0 and <= {@link LevenshteinAutomata#MAXIMUM_SUPPORTED_DISTANCE} .
     * @param transpositions <code>true</code> if transpositions should be treated as a primitive 
     *        edit operation. If this is false, comparisons will implement the classic
     *        Levenshtein algorithm.
     * @param nonFuzzyPrefix length of common (non-fuzzy) prefix
     * @param minFuzzyLength minimum length of lookup key before any edits are allowed
     * @param unicodeAware operate Unicode code points instead of bytes.
     */
    public FuzzyAutomatonConverter(int maxEdits, boolean transpositions, int nonFuzzyPrefix,
                          int minFuzzyLength, boolean unicodeAware) {
      super(unicodeAware);
      if (maxEdits < 0 || maxEdits > LevenshteinAutomata.MAXIMUM_SUPPORTED_DISTANCE) {
        throw new IllegalArgumentException("maxEdits must be between 0 and " + LevenshteinAutomata.MAXIMUM_SUPPORTED_DISTANCE);
      }
      if (nonFuzzyPrefix < 0) {
        throw new IllegalArgumentException("nonFuzzyPrefix must not be >= 0 (got " + nonFuzzyPrefix + ")");
      }
      if (minFuzzyLength < 0) {
        throw new IllegalArgumentException("minFuzzyLength must not be >= 0 (got " + minFuzzyLength + ")");
      }
      
      this.maxEdits = maxEdits;
      this.transpositions = transpositions;
      this.nonFuzzyPrefix = nonFuzzyPrefix;
      this.minFuzzyLength = minFuzzyLength;
    }
    
    @Override
    public <T> List<FSTUtil.Path<T>> getFullPrefixPaths(
        List<FSTUtil.Path<T>> prefixPaths, Automaton lookupAutomaton, FST<T> fst) throws IOException {
      // TODO: right now there's no penalty for fuzzy/edits,
      // ie a completion whose prefix matched exactly what the
      // user typed gets no boost over completions that
      // required an edit, which get no boost over completions
      // requiring two edits.  I suspect a multiplicative
      // factor is appropriate (eg, say a fuzzy match must be at
      // least 2X better weight than the non-fuzzy match to
      // "compete") ... in which case I think the wFST needs
      // to be log weights or something ...

      Automaton levA = convertAutomaton(toLevenshteinAutomata(lookupAutomaton));
      /*
        Writer w = new OutputStreamWriter(new FileOutputStream("out.dot"), "UTF-8");
        w.write(levA.toDot());
        w.close();
        System.out.println("Wrote LevA to out.dot");
      */
      return FSTUtil.intersectPrefixPaths(levA, fst);
    }

    @Override
    public Automaton convertAutomaton(Automaton a) {
      if (unicodeAware) {
        Automaton utf8automaton = new UTF32ToUTF8().convert(a);
        BasicOperations.determinize(utf8automaton);
        return utf8automaton;
      } else {
        return a;
      }
    }

    final Automaton toLevenshteinAutomata(Automaton automaton) {
      final Set<IntsRef> ref = SpecialOperations.getFiniteStrings(automaton, -1);
      Automaton subs[] = new Automaton[ref.size()];
      int upto = 0;
      for (IntsRef path : ref) {
        if (path.length <= nonFuzzyPrefix || path.length < minFuzzyLength) {
          subs[upto] = BasicAutomata.makeString(path.ints, path.offset, path.length);
          upto++;
        } else {
          Automaton prefix = BasicAutomata.makeString(path.ints, path.offset, nonFuzzyPrefix);
          int ints[] = new int[path.length-nonFuzzyPrefix];
          System.arraycopy(path.ints, path.offset+nonFuzzyPrefix, ints, 0, ints.length);
          // TODO: maybe add alphaMin to LevenshteinAutomata,
          // and pass 1 instead of 0?  We probably don't want
          // to allow the trailing dedup bytes to be
          // edited... but then 0 byte is "in general" allowed
          // on input (but not in UTF8).
          LevenshteinAutomata lev = new LevenshteinAutomata(ints, unicodeAware ? Character.MAX_CODE_POINT : 255, transpositions);
          Automaton levAutomaton = lev.toAutomaton(maxEdits);
          Automaton combined = BasicOperations.concatenate(Arrays.asList(prefix, levAutomaton));
          combined.setDeterministic(true); // its like the special case in concatenate itself, except we cloneExpanded already
          subs[upto] = combined;
          upto++;
        }
      }

      if (subs.length == 0) {
        // automaton is empty, there is no accepted paths through it
        return BasicAutomata.makeEmpty(); // matches nothing
      } else if (subs.length == 1) {
        // no synonyms or anything: just a single path through the tokenstream
        return subs[0];
      } else {
        // multiple paths: this is really scary! is it slow?
        // maybe we should not do this and throw UOE?
        Automaton a = BasicOperations.union(Arrays.asList(subs));
        // TODO: we could call toLevenshteinAutomata() before det? 
        // this only happens if you have multiple paths anyway (e.g. synonyms)
        BasicOperations.determinize(a);

        return a;
      }
    }
  }
  
}
