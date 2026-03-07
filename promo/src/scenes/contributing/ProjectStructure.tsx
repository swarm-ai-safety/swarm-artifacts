import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

const dirs = [
  { name: "swarm/agents/", desc: "Agent implementations", color: colors.accent },
  { name: "swarm/core/", desc: "Orchestrator, payoff, proxy", color: colors.success },
  { name: "swarm/governance/", desc: "Taxes, circuit breakers, sanctions", color: colors.warning },
  { name: "swarm/metrics/", desc: "Toxicity, quality gap, incoherence", color: colors.danger },
  { name: "swarm/models/", desc: "Data models and interactions", color: colors.textDim },
  { name: "swarm/bridges/", desc: "External framework integrations", color: colors.accentDim },
  { name: "tests/", desc: "Test suite with fixtures", color: colors.success },
  { name: "scenarios/", desc: "YAML scenario definitions", color: colors.warning },
];

export const ProjectStructure: React.FC = () => {
  const frame = useCurrentFrame();

  const headerProgress = spring({ frame, fps: 30, config: { damping: 200 } });

  return (
    <AbsoluteFill
      style={{
        background: colors.bg,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        fontFamily: fonts.heading,
        padding: 80,
      }}
    >
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundImage: `
            linear-gradient(${colors.gridLine} 1px, transparent 1px),
            linear-gradient(90deg, ${colors.gridLine} 1px, transparent 1px)
          `,
          backgroundSize: "80px 80px",
          opacity: 0.2,
        }}
      />

      <div
        style={{
          fontSize: 56,
          fontWeight: 800,
          color: colors.text,
          opacity: headerProgress,
          marginBottom: 50,
        }}
      >
        Know the Codebase
      </div>

      <div
        style={{
          display: "grid",
          gridTemplateColumns: "1fr 1fr",
          gap: "16px 40px",
          maxWidth: 1000,
          width: "100%",
        }}
      >
        {dirs.map((dir, i) => {
          const delay = 10 + i * 12;
          const progress = spring({
            frame: frame - delay,
            fps: 30,
            config: { damping: 200 },
          });
          const p = Math.max(0, progress);

          return (
            <div
              key={i}
              style={{
                display: "flex",
                alignItems: "center",
                gap: 16,
                opacity: p,
                transform: `translateY(${interpolate(p, [0, 1], [20, 0])}px)`,
                padding: "12px 16px",
                borderRadius: 10,
                background: `${dir.color}08`,
                borderLeft: `3px solid ${dir.color}40`,
              }}
            >
              <div>
                <div
                  style={{
                    fontSize: 20,
                    fontWeight: 700,
                    fontFamily: fonts.mono,
                    color: dir.color,
                  }}
                >
                  {dir.name}
                </div>
                <div
                  style={{
                    fontSize: 16,
                    color: colors.textDim,
                    marginTop: 2,
                  }}
                >
                  {dir.desc}
                </div>
              </div>
            </div>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};
