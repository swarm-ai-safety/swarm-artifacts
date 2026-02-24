import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

// Simulated agent positions on isometric grid
const AGENTS = [
  { id: 0, color: "#00FF88", baseX: 300, baseY: 600 },
  { id: 1, color: "#FF9500", baseX: 700, baseY: 500 },
  { id: 2, color: "#A855F7", baseX: 500, baseY: 750 },
  { id: 3, color: "#FF3B5C", baseX: 200, baseY: 850 },
  { id: 4, color: "#00E5FF", baseX: 800, baseY: 700 },
  { id: 5, color: "#FACC15", baseX: 450, baseY: 550 },
  { id: 6, color: "#00FF88", baseX: 600, baseY: 900 },
  { id: 7, color: "#FF9500", baseX: 350, baseY: 450 },
];

// Interaction arcs between agents with p-values
const ARCS = [
  { from: 0, to: 1, p: 0.92, delay: 40 },
  { from: 2, to: 3, p: 0.15, delay: 70 },
  { from: 4, to: 5, p: 0.78, delay: 100 },
  { from: 1, to: 6, p: 0.45, delay: 130 },
  { from: 7, to: 0, p: 0.88, delay: 155 },
  { from: 3, to: 4, p: 0.22, delay: 180 },
];

const METRICS = [
  { label: "Toxicity", value: 0.12, color: colors.danger },
  { label: "Quality Gap", value: -0.08, color: colors.warning },
  { label: "Gini", value: 0.34, color: colors.accent },
  { label: "Avg P", value: 0.71, color: colors.success },
];

function pColor(p: number): string {
  if (p > 0.7) return colors.success;
  if (p > 0.4) return colors.warning;
  return colors.danger;
}

export const GameplayPreview: React.FC = () => {
  const frame = useCurrentFrame();

  // Grid fade in
  const gridP = Math.max(
    0,
    spring({ frame, fps: 30, config: { damping: 100 } }),
  );

  // Metrics panel
  const metricsP = Math.max(
    0,
    spring({ frame: frame - 140, fps: 30, config: { damping: 200 } }),
  );

  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(ellipse at 50% 45%, ${colors.accentDim}10, ${colors.bg} 70%)`,
        fontFamily: fonts.heading,
      }}
    >
      {/* Grid overlay */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundImage: `
            linear-gradient(${colors.gridLine} 1px, transparent 1px),
            linear-gradient(90deg, ${colors.gridLine} 1px, transparent 1px)
          `,
          backgroundSize: "80px 80px",
          opacity: 0.3,
        }}
      />

      {/* Isometric grid */}
      <svg
        style={{ position: "absolute", top: 200, left: 0, opacity: gridP * 0.25 }}
        width={1080}
        height={800}
        viewBox="0 0 1080 800"
      >
        {Array.from({ length: 10 }, (_, i) => {
          const y = 100 + i * 70;
          return (
            <React.Fragment key={i}>
              <line
                x1={40}
                y1={y}
                x2={1040}
                y2={y}
                stroke={colors.accent}
                strokeWidth={0.5}
              />
              <line
                x1={40 + i * 100}
                y1={100}
                x2={40 + i * 100}
                y2={730}
                stroke={colors.accent}
                strokeWidth={0.5}
              />
            </React.Fragment>
          );
        })}
      </svg>

      {/* Agents and arcs */}
      <svg
        style={{ position: "absolute", top: 200, left: 0 }}
        width={1080}
        height={800}
        viewBox="0 0 1080 800"
      >
        {/* Interaction arcs */}
        {ARCS.map((arc, i) => {
          const arcP = Math.max(
            0,
            spring({ frame: frame - arc.delay, fps: 30, config: { damping: 100 } }),
          );
          if (arcP <= 0) return null;

          const a = AGENTS[arc.from];
          const b = AGENTS[arc.to];
          const mx = (a.baseX + b.baseX) / 2;
          const my = (a.baseY + b.baseY) / 2 - 80;
          const lineColor = pColor(arc.p);

          // Arc fades out after appearing
          const fadeOut = frame > arc.delay + 40
            ? Math.max(0, 1 - (frame - arc.delay - 40) / 30)
            : 1;

          return (
            <g key={i} opacity={arcP * fadeOut}>
              <path
                d={`M ${a.baseX} ${a.baseY - 200} Q ${mx} ${my - 200} ${b.baseX} ${b.baseY - 200}`}
                fill="none"
                stroke={lineColor}
                strokeWidth={2.5}
                strokeDasharray={`${arcP * 200} 200`}
              />
              {/* p-value label */}
              <text
                x={mx}
                y={my - 210}
                textAnchor="middle"
                fill={lineColor}
                fontSize={20}
                fontFamily={fonts.mono}
                opacity={arcP}
              >
                p={arc.p.toFixed(2)}
              </text>
            </g>
          );
        })}

        {/* Agent circles */}
        {AGENTS.map((agent, i) => {
          const delay = 10 + i * 8;
          const p = Math.max(
            0,
            spring({ frame: frame - delay, fps: 30, config: { damping: 200 } }),
          );
          // Gentle movement
          const dx = Math.sin(frame * 0.03 + i * 2.1) * 15;
          const dy = Math.cos(frame * 0.025 + i * 1.7) * 10;

          return (
            <g key={i} opacity={p}>
              {/* Glow */}
              <circle
                cx={agent.baseX + dx}
                cy={agent.baseY - 200 + dy}
                r={interpolate(p, [0, 1], [0, 28])}
                fill={`${agent.color}20`}
              />
              {/* Agent dot */}
              <circle
                cx={agent.baseX + dx}
                cy={agent.baseY - 200 + dy}
                r={interpolate(p, [0, 1], [0, 14])}
                fill={agent.color}
              />
            </g>
          );
        })}
      </svg>

      {/* Metrics panel */}
      <div
        style={{
          position: "absolute",
          bottom: 160,
          left: 60,
          right: 60,
          opacity: metricsP,
          transform: `translateY(${interpolate(metricsP, [0, 1], [40, 0])}px)`,
          background: `${colors.bg}E0`,
          border: `1px solid ${colors.accent}30`,
          borderRadius: 16,
          padding: "28px 36px",
          display: "flex",
          flexDirection: "column",
          gap: 20,
        }}
      >
        <div
          style={{
            fontSize: 22,
            color: colors.textDim,
            letterSpacing: "0.12em",
            textTransform: "uppercase",
            marginBottom: 8,
          }}
        >
          Live Metrics
        </div>
        {METRICS.map((m, i) => {
          const metricDelay = 150 + i * 12;
          const mP = Math.max(
            0,
            spring({ frame: frame - metricDelay, fps: 30, config: { damping: 50 } }),
          );
          const displayVal = interpolate(mP, [0, 1], [0, m.value]);

          return (
            <div
              key={m.label}
              style={{
                display: "flex",
                justifyContent: "space-between",
                alignItems: "center",
                opacity: mP,
              }}
            >
              <span style={{ fontSize: 30, color: colors.text, fontWeight: 500 }}>
                {m.label}
              </span>
              <span
                style={{
                  fontSize: 34,
                  fontFamily: fonts.mono,
                  color: m.color,
                  fontWeight: 700,
                }}
              >
                {displayVal.toFixed(2)}
              </span>
            </div>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};
