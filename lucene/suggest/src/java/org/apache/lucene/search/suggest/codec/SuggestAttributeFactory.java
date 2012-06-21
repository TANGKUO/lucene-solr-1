package org.apache.lucene.search.suggest.codec;

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

import java.text.Collator;

import org.apache.lucene.collation.tokenattributes.CollatedTermAttributeImpl;
import org.apache.lucene.util.Attribute;
import org.apache.lucene.util.AttributeImpl;
import org.apache.lucene.util.AttributeSource;

/**
 */
public class SuggestAttributeFactory extends AttributeSource.AttributeFactory {
  private final TermWeightProcessor processor;
  private final AttributeSource.AttributeFactory delegate;
  
  public SuggestAttributeFactory(TermWeightProcessor collator) {
    this(AttributeSource.AttributeFactory.DEFAULT_ATTRIBUTE_FACTORY, collator);
  }
  
  public SuggestAttributeFactory(AttributeSource.AttributeFactory delegate, TermWeightProcessor collator) {
    this.delegate = delegate;
    this.processor = collator;
  }
  
  @Override
  public AttributeImpl createAttributeInstance(
      Class<? extends Attribute> attClass) {
    return attClass.isAssignableFrom(SuggestAttributeFactory.class)
    ? new SuggestTermAttributeImpl(processor)
    : delegate.createAttributeInstance(attClass);
  }
}
