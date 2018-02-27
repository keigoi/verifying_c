// A priority queue implementation from MySQL 5.7
// The original version is at https://raw.githubusercontent.com/mysql/mysql-server/21e162518cf72802e295d0858ce59edd1d455218/mysys/queues.c

/* Copyright (c) 2000, 2015, Oracle and/or its affiliates. All rights reserved.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; version 2 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA */

/*
  Code for handling of priority Queues.
  Implemention of queues from "Algoritms in C" by Robert Sedgewick.
  An optimisation of _downheap suggested in Exercise 7.51 in "Data
  Structures & Algorithms in C++" by Mark Allen Weiss, Second Edition
  was implemented by Mikael Ronstrom 2005. Also the O(N) algorithm
  of queue_fix was implemented.
*/

#include "queues.h"

#include <stdlib.h>
#include <assert.h>

#define DBUG_ENTER(s)
#define DBUG_RETURN(e) return (e)
#define DBUG_VOID_RETURN return
#define DBUG_ASSERT

typedef char    my_bool;
#define TRUE 1
#define FALSE 0

/*@
// Theorems which Z3 cannot prove (?) 
lemma void mult_div_by_2_is_identity(int i);
  requires 0 < i; // &*& i < INT_MAX/2;
  ensures i*2/2 == i;

lemma void mult_div_by_2_is_identity_ex(int i);
  requires 0 < i; // &*& i < INT_MAX/2-1;
  ensures (i*2+1)/2 == i;

lemma void div_mult_le_orig(int i);
  requires 0 < i; // &*& i < INT_MAX/2;
  ensures i / 2 * 2 <= i;

lemma void div_mult_ge_orig(int i);
  requires 0 < i; // &*& i < INT_MAX/2;
  ensures i <= i / 2 * 2 + 1;

lemma void div_by_2_is_not_same_as_before(int i);
  requires i != 0;
  ensures i/2 != i;

lemma void div_mult_monotone(int i, int n);
  requires 0 < i &*& n / 2 < i; // &*& i < INT_MAX/2;
  ensures n < i * 2;

lemma void div_by_2_ge_0(int i);
  requires i >= 0;
  ensures i/2 >= 0;

lemma void div_by_2_ge_1(int i);
  requires i > 1;
  ensures i/2 >= 1;

lemma void div_by_2_monotone(int i, int n);
  requires i <= n &*& n > 0;
  ensures i/2 < n;

lemma void mult_by_2_preserves_lt(int n, int i);
  requires n < i &*& n >= 0;
  ensures n*2+1 < i*2;

lemma void shift_right_by_one_is_div_by_2(int i);
  requires i>=0;
  ensures (i >> 1) == i / 2;

lemma void shift_right_by_one_ge_0(int i);
  requires i >= 0;
  ensures (i >> 1) >= 0;

@*/

/*@
// TODO ============================

lemma void dispose_elements_over_hole_less_than();
  requires elements_over_hole_less_than(?values, ?idx, ?hole, ?element);
  ensures true;

lemma void dispose_doubles();
  requires doubles(?i, ?j);
  ensures true;

lemma void heap_update_preserves_subheap(int i, int hole, list<int> values, int element);
  requires is_heap(values, i, ?elements) &*& hole < i;
  ensures is_heap(update(hole, element, values), i, elements);

lemma void heap_hole_move_down(list<int> values, int idx);
   requires 
     is_heap_with_hole(values, 1, ?elements, idx, ?hole_elt) 
     &*& elements_over_hole_less_than(values, 1, ?hole, hole_elt);
   ensures 
     (idx + idx < elements && nth(idx + idx, values) > nth(idx + idx + 1, values))
       ? is_heap_with_hole(update(idx, nth(idx + idx + 1, values), values), 1, elements, idx + idx + 1, hole_elt)
         &*& elements_over_hole_less_than(update(idx, nth(idx + idx + 1, values), values), 1, hole, hole_elt)
       : is_heap_with_hole(update(idx, nth(idx + idx, values), values), 1, elements, idx + idx, hole_elt)
         &*& elements_over_hole_less_than(update(idx, nth(idx + idx, values), values), 1, hole, hole_elt);

lemma void heap_hole_move_up(list<int> values, int idx, int next_index);
   requires 
     is_heap_with_hole(values, 1, ?elements, idx, ?hole_elt)
     &*& elements_over_hole_less_than(values, 1, ?start_idx, hole_elt);
   ensures 
     is_heap_with_hole(update(idx, nth(next_index, values), values), 1, elements, next_index, hole_elt)
     &*& elements_over_hole_less_than(update(idx, nth(next_index, values), values), 1, start_idx, hole_elt)
     &*& nth(next_index, update(idx, nth(next_index, values), values)) <= nth(next_index*2, update(idx, nth(next_index, values), values))
     &*& nth(next_index, update(idx, nth(next_index, values), values)) <= nth(next_index*2+1, update(idx, nth(next_index, values), values))
     &*& hole_elt <= nth(idx, update(idx, nth(next_index, values), values))
   ;

  @*/

/*@
predicate is_heap(list<int> values, int i, int count) =
    i < count
      ? nth(i/2, values) <= nth(i, values)
        &*& is_heap(values, i*2, count) 
        &*& is_heap(values, i*2+1, count)
      : true;

predicate is_heap_with_parent_value(list<int> values, int i, int count, int parent_value) =
    i < count
      ? parent_value <= nth(i, values)
        &*& is_heap(values, i*2, count) 
        &*& is_heap(values, i*2+1, count)
      : true;

predicate is_heap_with_hole(list<int> values, int i, int elements, int hole, int hole_elt) =
  1<=hole &*& hole <= elements &*&
  (i < elements 
  ? i < hole
    ? nth(i/2, values) <= nth(i, values)
            &*& is_heap_with_hole(values, i*2, elements, hole, hole_elt) 
            &*& is_heap_with_hole(values, i*2+1, elements, hole, hole_elt)
    : (i == hole 
      ? nth(i/2, values) <= hole_elt
        &*& is_heap_with_parent_value(values, i*2, elements, nth(i/2, values)) 
        &*& is_heap_with_parent_value(values, i*2+1, elements, nth(i/2, values))
      : is_heap(values, i, elements) // hole < i
      )
  : true);
 
predicate is_queue(QUEUE *queue, int count) =
    queue->elements |-> count &*& queue->root |-> ?root 
    &*& queue->max_elements |-> ?max_elements
    &*& count < max_elements
    &*& malloc_block_st_queue(queue) &*& ints(root, (max_elements + 1), ?values)
    &*& malloc_block_ints(root, (max_elements + 1))
    &*& is_heap(values, 1, count);

predicate elements_over_hole_less_than(list<int> values, int i, int hole, int element) =
  0 < i &*& i < length(values) 
  &*& (i <= hole 
   ? nth(i, values) <= element &*& elements_over_hole_less_than(values, i+1, hole, element)
   : true);

predicate hole_leq_subheap(list<int> values, int elements, int i, int hole) =
  0 < i &*& i < length(values)
  &*& 0 < elements &*& elements < length(values)
  &*& 0 < hole &*& hole < elements
  &*& (hole <= i
   ? nth(hole, values) <= nth(i, values)
     &*& hole_leq_subheap(values, elements, i*2, hole) 
     &*& hole_leq_subheap(values, elements, i*2+1, hole)
   : true);
    
predicate is_queue_with_hole(QUEUE *queue, int elements, int hole, int hole_elt) =
    queue->root |-> ?root 
    &*& queue->elements |-> elements
    &*& queue->max_elements |-> ?max_elements 
    &*& malloc_block_st_queue(queue)
    &*& ints(root, (max_elements + 1), ?values)
    &*& malloc_block_ints(root, (max_elements + 1))
    &*& 0 < hole &*& hole < max_elements + 1
    &*& elements < max_elements
    &*& 0 < max_elements + 1
    &*& is_heap_with_hole(values, 1, elements, hole, hole_elt)
    &*& elements_over_hole_less_than(values, 1, hole, hole_elt)
    &*& hole_elt == nth(hole, values);

predicate doubles(int start_idx, int idx) =
  start_idx > idx
    ? false
    : (start_idx == idx 
      ? true
      : doubles(start_idx, idx/2));
@*/

/*@
lemma void apply_elements_over_hole_less_than_ex(list<int> values, int i, int n, int hole, int element)
  requires elements_over_hole_less_than(values, i, hole, element) &*& 1 <= n &*& n <= hole &*& i <= n;
  ensures elements_over_hole_less_than(values, n, hole, element);
{
  if (i == n) {
    // skip
  } else if (i < n) {
    open elements_over_hole_less_than(values, i, hole, element);
    apply_elements_over_hole_less_than_ex(values, i+1, n, hole, element);
  }
}

lemma void apply_elements_over_hole_less_than(list<int> values, int n, int hole, int element)
  requires elements_over_hole_less_than(values, 1, hole, element) &*& 1 <= n &*& n <= hole;
  ensures elements_over_hole_less_than(values, n, hole, element);
{
  apply_elements_over_hole_less_than_ex(values, 1, n, hole, element);
}

lemma void heap_condition_recovered(int i, int hole, list<int> values, int hole_elt)
   requires 
     is_heap_with_hole(values, i, ?elements, hole, hole_elt) 
     &*& 0 < i
     &*& (1 <= hole/2 ? nth(hole/2, values) <= hole_elt : true)
     &*& (hole*2 < elements 
          ? hole_elt <= nth(hole*2, values) 
            &*& (hole*2+1 < elements
                ? hole_elt <= nth(hole*2+1, values)
                : true)
          : true)
     &*& elements < length(values);
   ensures is_heap(update(hole, hole_elt, values), i, elements);
{  
   // assumptions
   mult_div_by_2_is_identity(i);
   mult_div_by_2_is_identity_ex(i);
   div_by_2_is_not_same_as_before(i);
   div_by_2_ge_0(i);

   if(i >= elements) {
      open is_heap_with_hole(values, i, elements, hole, hole_elt);
      close is_heap(update(hole, hole_elt, values), i, elements);
   } else if(i == hole) {
      div_by_2_monotone(i, length(values));

      if(hole*2 < elements){
        open is_heap_with_hole(values, i, elements, hole, hole_elt);
        open is_heap_with_parent_value(values, i*2, elements, nth(i/2, values));
        open is_heap_with_parent_value(values, i*2+1, elements, nth(i/2, values));
        heap_update_preserves_subheap(i*2*2, hole, values, hole_elt);
        heap_update_preserves_subheap(i*2*2+1, hole, values, hole_elt);
        if (i * 2 + 1 < elements) {
          heap_update_preserves_subheap((i*2+1)*2, hole, values, hole_elt);
          heap_update_preserves_subheap((i*2+1)*2+1, hole, values, hole_elt);
        }
        close is_heap(update(hole, hole_elt, values), i*2, elements);
        close is_heap(update(hole, hole_elt, values), i*2+1, elements);
        close is_heap(update(hole, hole_elt, values), i, elements);
      } else {
        open is_heap_with_hole(values, i, elements, hole, hole_elt);
        open is_heap_with_parent_value(values, i*2, elements, nth(i/2, values));
        open is_heap_with_parent_value(values, i*2+1, elements, nth(i/2, values));
        close is_heap(update(hole, hole_elt, values), i*2, elements);
        close is_heap(update(hole, hole_elt, values), i*2+1, elements);
        close is_heap(update(hole, hole_elt, values), i, elements);
      }
   } else if(i < hole) {
      open is_heap_with_hole(values, i, elements, hole, hole_elt);
      heap_condition_recovered(i*2, hole, values, hole_elt);
      heap_condition_recovered(i*2+1, hole, values, hole_elt);
      div_by_2_monotone(i, hole);
      assert nth(i/2, update(hole, hole_elt, values)) <= nth(i, update(hole, hole_elt, values));
      close is_heap(update(hole, hole_elt, values), i, elements);
   } else if(i < elements) { // hole < i
      open is_heap_with_hole(values, i, elements, hole, hole_elt);
      heap_update_preserves_subheap(i, hole, values, hole_elt);
   }
}
@*/


	/* Remove item from queue */
	/* Returns pointer to removed element */

int queue_remove(QUEUE *queue, uint idx)
/// requires is_queue(queue, ?elements) &*& (0 <= idx && idx < elements);
/// ensures is_queue(queue, elements-1);
{
  int element;
  //@ open is_queue(queue, elements);
  //@ assert( ints(_, _, ?values) );
  //@ open is_heap(values, 1, elements);
  DBUG_ASSERT(idx < queue->max_elements);
  idx++;
  element= queue->root[idx];  /* Intern index starts from 1 */
  queue->root[idx]= queue->root[queue->elements];
  queue->elements--;
  //@ assert( ints(_, _, ?values2) );
  //@ close is_heap_with_hole(values2, 1, elements-1, idx, nth(idx, values));
  //@ close is_queue_with_hole(queue, elements-1, idx, element);
  _downheap(queue, idx);
  return element;
}


void _downheap(QUEUE *queue, uint idx)
//@ requires is_queue_with_hole(queue, ?elements0, idx, ?_element) &*& elements0 > 0 &*& 1 <= idx &*& idx <= elements0; 
//@ ensures is_queue(queue, elements0);
{
  int element;
  uint elements,half_queue, next_index;
  my_bool first= TRUE;
  uint start_idx= idx;
  //@ close doubles(start_idx, idx);

  //@ open is_queue_with_hole(queue, elements0, idx, _element);
  //@ assert( ints(?root, ?max_elements0, _) );

  element=queue->root[idx];
  elements=queue->elements;
  /* half_queue=elements >> 1; */half_queue=elements / 2;
  
  while (idx <= half_queue)
  /*@ invariant 
          ints(root, max_elements0, ?values_inv)
      &*& (0 < idx && idx < max_elements0)
      &*& is_heap_with_hole(values_inv, 1, elements0, idx, element)
      &*& (start_idx <= half_queue // do we enter the loop?
          ? (first==TRUE || (first==FALSE && nth(idx/2, values_inv) <= nth(idx, values_inv)))
          : first==TRUE)
      &*& (first==TRUE 
          ? start_idx == idx 
          : (first==FALSE 
             && start_idx < idx 
             && nth(idx, values_inv) == nth(idx/2, values_inv)))
      &*& doubles(start_idx, idx)
      // for returning
      &*& elements_over_hole_less_than(values_inv, 1, start_idx, element)
      &*& queue->root |-> root 
      &*& queue->elements |-> elements0
      &*& queue->max_elements |-> max_elements0 - 1
      &*& malloc_block_st_queue(queue)
      &*& malloc_block_ints(root, max_elements0);
  @*/   
  {
    //@ div_mult_le_orig(elements);
    //@ div_by_2_monotone(idx, idx);
    //@ mult_div_by_2_is_identity(idx);
    //@ mult_div_by_2_is_identity_ex(idx);
    
    next_index=idx+idx;
    if (next_index < elements &&
	queue->root[next_index] > queue->root[next_index+1])
      next_index++;
    if (first==TRUE &&
	queue->root[next_index] >= element)
    {
      //@ assert start_idx == idx;
      queue->root[idx]= element;
      /*@
          if (idx>1) {
            div_by_2_ge_1(idx);
            apply_elements_over_hole_less_than(values_inv, idx/2, start_idx, element);
            open elements_over_hole_less_than(values_inv, idx/2, start_idx, element);
          }
        @*/
      //@ heap_condition_recovered(1, idx, values_inv, element);
      //@ close is_queue(queue, elements0);
      //@ dispose_elements_over_hole_less_than();
      //@ dispose_doubles();
      return;
    }
    queue->root[idx]=queue->root[next_index];
    //@ heap_hole_move_down(values_inv, idx);
    //@ assert is_heap_with_hole(?values2, 1, elements0, next_index, element);
    //@ assert idx == next_index/2;
    idx=next_index;
    //@ close doubles(start_idx, idx);
    
    first= FALSE;

  }
  //@ div_by_2_monotone(idx, idx);
  //@ div_by_2_ge_0(idx);
  //@ div_mult_monotone(idx, elements);
  
  /* next_index= idx >> 1; */next_index= idx / 2;
  
  while (next_index > start_idx)
  /*@ invariant queue->root |-> root 
      &*& ints(root, max_elements0, ?values_inv1)
      &*& is_heap_with_hole(values_inv1, 1, elements, idx, element)
      &*& elements_over_hole_less_than(values_inv1, 1, start_idx, element)
      &*& 0 <= next_index &*& next_index < max_elements0
      &*& 0 <= idx &*& idx < max_elements0
      &*& doubles(start_idx, idx)
      &*& idx > 0
      &*& idx / 2 == next_index
      &*& idx > next_index
      &*& (idx*2 > elements || nth(idx, values_inv1) <= nth(idx*2, values_inv1))
      &*& (idx*2+1 > elements || nth(idx, values_inv1) <= nth(idx*2+1, values_inv1))
      &*& (idx*2 > elements || element <= nth(idx*2, values_inv1))
      &*& (idx*2+1 > elements || element <= nth(idx*2+1, values_inv1))
      ;
  @*/   
  {
    if (queue->root[next_index] < element)
      break;
    queue->root[idx]=queue->root[next_index];
    //@ heap_hole_move_up(values_inv1, idx, next_index);
    //@ open doubles(start_idx, idx);
    idx=next_index;
    /* next_index= idx >> 1; */next_index= idx / 2;

    //@ div_by_2_monotone(idx, idx);
    //@ div_by_2_ge_0(idx);
  }
  //@ assert ints(root, max_elements0, ?values_inv2);
  
  queue->root[idx]=element;
  
  /*@ if (next_index<=start_idx) {
        if (idx>1) {
          div_by_2_ge_1(idx);
          apply_elements_over_hole_less_than(values_inv2, idx/2, start_idx, element);
          open elements_over_hole_less_than(values_inv2, idx/2, start_idx, element);
        }
      }
    @*/
 
  //@ open doubles(start_idx, idx);
  //@ dispose_elements_over_hole_less_than();
  /*@ if (start_idx!=idx) {
       dispose_doubles();
      }
   @*/

  //@ heap_condition_recovered(1, idx, values_inv2, element);
  //@ close is_queue(queue, elements);
}
