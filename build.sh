#!/bin/sh
racc lang.y.rb && ruby lang.tab.rb
