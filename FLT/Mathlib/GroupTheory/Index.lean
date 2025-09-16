import Mathlib.GroupTheory.Index

-- #24184
-- This is cool notation. Should mathlib have it? And what should the `relindex` version be?
scoped[GroupTheory] notation "[" G ":" H "]" => @AddSubgroup.index G _ H
