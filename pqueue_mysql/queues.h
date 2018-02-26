// A priority queue implementation from MySQL 5.7
// The original version is at https://raw.githubusercontent.com/mysql/mysql-server/6eabb89c033a436d6b92dc317ffc59d68e99140e/include/queues.h

/* Copyright (c) 2000, 2014, Oracle and/or its affiliates. All rights reserved.

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

#ifndef QUEUES_INCLUDED
#define QUEUES_INCLUDED

/*
  Code for handling of priority Queues.
  Implemention of queues from "Algoritms in C" by Robert Sedgewick.
  By monty.
*/

#define NULL ((void*) 0)
#define inline

typedef unsigned int uint;
typedef unsigned char uchar;
typedef char	pchar;
typedef char	pbool;
typedef char    my_bool;
typedef int compare_fun(void * env, uchar * a,uchar * b);

#ifdef	__cplusplus
extern "C" {
#endif

typedef struct st_queue {
  uchar **root;
  void *first_cmp_arg;
  uint elements;
  uint max_elements;
  uint offset_to_key;	/* compare is done on element+offset */
  int max_at_top;	/* Normally 1, set to -1 if queue_top gives max */
  compare_fun *compare;
  uint auto_extent;
} QUEUE;

void _downheap(QUEUE *queue,uint idx);

uchar *queue_remove(QUEUE *queue,uint idx);

#endif  // QUEUES_INCLUDED
