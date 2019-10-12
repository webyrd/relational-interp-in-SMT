#!/bin/bash

cvc4 --lang smt --fmf-fun -m --incremental $1
