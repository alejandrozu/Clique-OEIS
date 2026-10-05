#requires -Version 7.0
param([string]$OutFile = (Join-Path $PSScriptRoot '../work/census_n8_powershell.json'))
$ErrorActionPreference = 'Stop'
# Independent exhaustive census of all 2^28 simple graphs on eight labeled vertices.
# For each seven-vertex graph, compute all induced-subgraph clique numbers using
# omega(S)=max(omega(S\v),1+omega((S\v) intersect N(v))). Then add vertex eight
# with each of its 128 possible neighborhoods. No original verification code used.
Add-Type -TypeDefinition @'
using System;
using System.Numerics;
public static class IndependentCliqueCensus8 {
    public static long[][] Run() {
        long[][] hist = new long[9][];
        for(int k=0;k<=8;k++) hist[k]=new long[29];
        int[] adj=new int[7], om=new int[128], pc=new int[128];
        int[] eu=new int[21],ev=new int[21];
        int t=0;
        for(int u=0;u<7;u++)for(int v=u+1;v<7;v++){eu[t]=u;ev[t++]=v;}
        for(int s=1;s<128;s++)pc[s]=pc[s&(s-1)]+1;
        int edges=0;
        for(int g=0;g<(1<<21);g++) {
            if(g>0) {
                int bit=BitOperations.TrailingZeroCount((uint)g);
                int u=eu[bit],v=ev[bit];
                bool wasEdge=(adj[u]&(1<<v))!=0;
                adj[u]^=1<<v;adj[v]^=1<<u;
                edges+=wasEdge?-1:1;
            }
            for(int s=1;s<128;s++) {
                int v=BitOperations.TrailingZeroCount((uint)s);
                int rest=s&(s-1);
                int a=om[rest],b=1+om[rest&adj[v]];
                om[s]=a>b?a:b;
            }
            int baseOmega=om[127];
            for(int ns=0;ns<128;ns++) {
                int a=baseOmega,b=1+om[ns];
                hist[a>b?a:b][edges+pc[ns]]++;
            }
        }
        return hist;
    }
}
'@
$timer = [System.Diagnostics.Stopwatch]::StartNew()
$hist = [IndependentCliqueCensus8]::Run()
$timer.Stop()
$result = [ordered]@{n=8;graphs_enumerated=268435456;elapsed_seconds=$timer.Elapsed.TotalSeconds;histogram_by_clique_then_edges=$hist}
$directory = Split-Path -Parent ([System.IO.Path]::GetFullPath($OutFile))
New-Item -ItemType Directory -Force -Path $directory | Out-Null
$result | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath $OutFile -Encoding utf8
Write-Output ('Completed exact eight-vertex census in {0:F2} seconds' -f $timer.Elapsed.TotalSeconds)
