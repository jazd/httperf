/*
    httperf -- a tool for measuring web server performance
    Copyright 2000-2007 Hewlett-Packard Company

    This file is part of httperf, a web server performance measurment
    tool.

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License as
    published by the Free Software Foundation; either version 2 of the
    License, or (at your option) any later version.
    
    In addition, as a special exception, the copyright holders give
    permission to link the code of this work with the OpenSSL project's
    "OpenSSL" library (or with modified versions of it that use the same
    license as the "OpenSSL" library), and distribute linked combinations
    including the two.  You must obey the GNU General Public License in
    all respects for all of the code used other than "OpenSSL".  If you
    modify this file, you may extend this exception to your version of the
    file, but you are not obligated to do so.  If you do not wish to do
    so, delete this exception statement from your version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  
    02110-1301, USA
*/

/* This load generator can be used to recreate a workload based on a
   server log file.
 
   This module can be used in conjunction with two comands to help in
   extracting information from the httpd CLF file (contact
   eranian@hpl.hp.com).
 
   Please note that you don't necessary need any of those tools. You
   can recreate the list of URIs by hand or with any other programs as
   long as you respect the format expected by this module (and also
   provided than you have the corresponding document tree on the
   server side).
 
   The format of the file used by this module is very simple (maybe
   too simple):

	URI1\0URI2\0......URIn\0
  
   It is a simple concatenated list of URI separated by the \0 (end of
   string) marker.
 
   This way, we don't need any parsing of the string when generating
   the URI.

   If, however, the --embedded-http-headers option is given, then the format
   is as follows:

   http-headers^AURI1\0http-headers^AYURI2\0...URIn\0

   Where, the requests are separated by the \0, and the http headers for
   each request are given before the first control-A character.  The headers
   are parsed exactly as they are when passed by --add-header.  However,
   each request is given it's own set of http headers.  (That is, the headers
   are not additive.)

   You can choose to loop on te list of URIs by using the following
   command line option to httperf:

       % httperf .... --wlog y,my_uri_file

   Otherwise httperf will stop once it reaches the end of the list.
 
   Any comment on this module contact eranian@hpl.hp.com or
   davidm@hpl.hp.com.  */

#include "config.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <generic_types.h>

#include <object.h>
#include <timer.h>
#include <httperf.h>
#include <call.h>
#include <conn.h>
#include <core.h>
#include <localevent.h>

static char *fbase, *fend, *fcurrent;

/* borrowed from src/gen/misc.c */
static const char *
unescape_local (const char *str, int *len)
{
  char *dp, *dst = strdup (str);
  const char *cp;
  int ch;

  if (!dst)
    panic ("%s: strdup() failed: %s\n", prog_name, strerror (errno));

  for (cp = str, dp = dst; (ch = *cp++); )
    {
      if (ch == '\\')
	{
	  ch = *cp++;
	  switch (ch)
	    {
	    case '\\':	/* \\ -> \ */
	      break;

	    case 'a':	/* \a -> LF */
	      ch = 10;
	      break;

	    case 'r':	/* \r -> CR */
	      ch = 13;
	      break;

	    case 'n':	/* \n -> CR/LF */
	      *dp++ = 13;
	      ch = 10;
	      break;

	    case '0': case '1': case '2': case '3': case '4':
	    case '5': case '6': case '7': case '8': case '9':
	      ch = strtol (cp - 1, (char **) &cp, 8);
	      break;

	    default:
	      fprintf (stderr, "%s: ignoring unknown escape sequence "
		       "`\\%c' in --add-header\n", prog_name, ch);
	      break;
	    }
	}
      *dp++ = ch;
    }
  *len = dp - dst;
  return dst;
}

static void
set_uri (Event_Type et, Call * c)
{
  int len, did_wrap = 0;
  const char *uri, *extra_request_headers, *extra_request_headers_escaped;
  char *ptr, *erh_2;
  int extra_request_headers_len, extra_request_headers_len2, len_to_advance;

  assert (et == EV_CALL_NEW && object_is_call (c));

  do
    {
      if (fcurrent >= fend)
	{
	  if (did_wrap)
	    panic ("%s: %s does not contain any valid URIs\n",
		   prog_name, param.wlog.file);
	  did_wrap = 1;

	  /* We reached the end of the uri list so wrap around to the
	     beginning.  If not looping, also ask for the test to stop
	     as soon as possible (the current request will still go
	     out, but httperf won't wait for its reply to show up).  */
	  fcurrent = fbase;
	  if (!param.wlog.do_loop)
	    core_exit ();
	}
      uri = fcurrent;
      len = strlen (fcurrent);
      len_to_advance = len;

      /* look for global option for embedded HTTP headers.
      if set, look for control-A separator.  If found, parse from fcurrent to ctrl-A as headers, and set ctrl-A+1 as uri.  Then set len to len -= strlen(headers)

      be sure that the extra (which is the headers itself) is unescaped
      -- unescape calls strdup, so it's safe to use the returned string

      */
      if (param.use_embedded_http_headers)
      {
        extra_request_headers = '\0';
        extra_request_headers = memchr(uri, '\1', len);
        if (extra_request_headers != '\0')
        {
          /* control-A character found ... swap variables so they make sense */
          ptr = (char *)uri;
          uri = extra_request_headers;
          uri++;
          extra_request_headers = ptr;
          /*
            now, uri points to the start of the URL to request
            and extra_request_headers points to the start of the http
            Loop thru the headers, find the \1, and replace it with \0.
          */

          extra_request_headers_len = 0;
          erh_2 = '\0';
          ptr = (char *)extra_request_headers;
          while (*ptr)
          {
            if (*ptr == '\1')
            {
                erh_2 = (char *)malloc(extra_request_headers_len+1);
                memset(erh_2, '\0', extra_request_headers_len+1);
                memcpy(erh_2, extra_request_headers, extra_request_headers_len);
                break;
            }
            ptr++;
            extra_request_headers_len++;
          }

          extra_request_headers_escaped =
            unescape_local(erh_2, &extra_request_headers_len2);
          if (erh_2)
            free(erh_2);
          if (DBG > 5)
            fprintf(stderr, "Generated http headers [%.*s] uri [%s]\n",
              extra_request_headers_len2, extra_request_headers_escaped, uri);

          call_append_request_header (c,
            extra_request_headers_escaped, extra_request_headers_len2);
          /* and reduce the length of the URI by the header length */
          len -= extra_request_headers_len + 1;

        }
      }

      call_set_uri (c, uri, len);
      fcurrent += len_to_advance + 1;
    }
  while (len == 0);

  if (verbose)
    printf ("%s: accessing URI `%s'\n", prog_name, uri);
}

void
init_wlog (void)
{
  struct stat st;
  Any_Type arg;
  int fd;

  fd = open (param.wlog.file, O_RDONLY, 0);
  if (fd == -1)
    panic ("%s: can't open %s\n", prog_name, param.wlog.file);

  fstat (fd, &st);
  if (st.st_size == 0)
    panic ("%s: file %s is empty\n", prog_name, param.wlog.file);

  /* mmap anywhere in address space: */
  fbase = (char *) mmap (0, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (fbase == (char *) -1)
    panic ("%s: can't mmap the file: %s\n", prog_name, strerror (errno));

  close (fd);

  /* set the upper boundary: */
  fend = fbase + st.st_size;
  /* set current entry: */
  fcurrent = fbase;

  arg.l = 0;
  event_register_handler (EV_CALL_NEW, (Event_Handler) set_uri, arg);
}

static void
stop_wlog (void)
{
  munmap (fbase, fend - fbase);
}

Load_Generator uri_wlog =
  {
    "Generates URIs based on a predetermined list",
    init_wlog,
    no_op,
    stop_wlog
  };
